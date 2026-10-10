import DistinctDistances.TrackC.Polynomial
import DistinctDistances.TrackC.PlanarBoundary
import DistinctDistances.TrackC.PartitionCauchy
import DistinctDistances.TrackC.RichLineTail
import DistinctDistances.TrackC.UniformRichLines
import DistinctDistances.TrackC.LinePartitionOptimization

open scoped BigOperators
open Classical

namespace DistinctDistances.TrackC

private theorem generic_linear_map_for_pairs {d : ℕ} (U : Finset (E d))
    (P : Finset (E d × E d))
    (hU : ∀ u ∈ U, u ≠ 0)
    (hPfirst : ∀ p ∈ P, p.1 ∈ U)
    (hPind : ∀ p ∈ P, LinearIndependent ℝ ![p.1, p.2]) :
    ∃ A : E d →ₗ[ℝ] E 2,
      (∀ u ∈ U, A u ≠ 0) ∧
      (∀ p ∈ P, LinearIndependent ℝ ![A p.1, A p.2]) := by
  classical
  letI : Fintype {u : E d // u ∈ U} := Fintype.ofFinset U (by simp)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) (M := E d)
    (fun u : {u : E d // u ∈ U} => u.1)
    (fun u => hU u.1 u.2)
  let w : {p : E d × E d // p ∈ P} → E d := fun p =>
    f p.1.1 • p.1.2 - f p.1.2 • p.1.1
  have hw (p : {p : E d × E d // p ∈ P}) : w p ≠ 0 := by
    by_contra hz
    have hfu : f p.1.1 ≠ 0 := hf ⟨p.1.1, hPfirst p.1 p.2⟩
    have hrel : (-f p.1.2) • p.1.1 + f p.1.1 • p.1.2 = 0 := by
      calc
        (-f p.1.2) • p.1.1 + f p.1.1 • p.1.2 =
            f p.1.1 • p.1.2 - f p.1.2 • p.1.1 := by module
        _ = w p := rfl
        _ = 0 := hz
    have hzero := (LinearIndependent.pair_iff.mp (hPind p.1 p.2))
      (-f p.1.2) (f p.1.1) hrel
    exact hfu hzero.2
  letI : Fintype {p : E d × E d // p ∈ P} := Fintype.ofFinset P (by simp)
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) (M := E d) w hw
  let e0 : E 2 := WithLp.toLp 2 ![(1 : ℝ), 0]
  let e1 : E 2 := WithLp.toLp 2 ![(0 : ℝ), 1]
  let A : E d →ₗ[ℝ] E 2 := {
    toFun := fun x => WithLp.toLp 2 ![f x, g x]
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp
    map_smul' := by
      intro a x
      ext i
      fin_cases i <;> simp
  }
  have hA_apply (x : E d) : A x = f x • e0 + g x • e1 := by
    ext i
    fin_cases i <;> simp [A, e0, e1]
  have he01 : LinearIndependent ℝ ![e0, e1] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h0 := congrArg (fun v : E 2 => v 0) hab
    have h1 := congrArg (fun v : E 2 => v 1) hab
    constructor
    · simpa [e0, e1] using h0
    · simpa [e0, e1] using h1
  have hdet (p : {p : E d × E d // p ∈ P}) :
      f p.1.1 * g p.1.2 ≠ g p.1.1 * f p.1.2 := by
    have hwg := hg p
    have hEval : g (w p) = f p.1.1 * g p.1.2 - f p.1.2 * g p.1.1 := by
      simp [w, map_sub, map_smul, mul_comm]
    have hne : f p.1.1 * g p.1.2 - f p.1.2 * g p.1.1 ≠ 0 := by
      simpa only [← hEval] using hwg
    intro heq
    apply hne
    rw [heq, mul_comm (f p.1.2) (g p.1.1)]
    exact sub_self _
  have hpair (p : {p : E d × E d // p ∈ P}) :
      LinearIndependent ℝ ![A p.1.1, A p.1.2] := by
    rw [hA_apply, hA_apply, LinearIndependent.pair_add_smul_add_smul_iff]
    exact ⟨he01, hdet p⟩
  refine ⟨A, ?_, ?_⟩
  · intro u hu hzero
    have hcoord : f u = 0 := by
      have h := congrArg (fun v : E 2 => v 0) hzero
      simpa [A] using h
    exact hf ⟨u, hu⟩ hcoord
  · intro p hp
    exact hpair ⟨p, hp⟩

private theorem vsub_pair_independent_iff_not_collinear {d : ℕ} {x y z : E d} :
    LinearIndependent ℝ ![y - x, z - x] ↔
      ¬ Collinear ℝ ({x, y, z} : Set (E d)) := by
  let p : Fin 3 → E d := ![x, y, z]
  let f : Fin 2 → {i : Fin 3 // i ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.succ_injective 2
      exact congrArg Subtype.val hij
    · intro i
      obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero i.2
      exact ⟨j, Subtype.ext hj⟩
  let e : Fin 2 ≃ {i : Fin 3 // i ≠ 0} := Equiv.ofBijective f hf
  have hfun :
      (fun i : Fin 2 => p (e i).1 -ᵥ p 0) = ![y - x, z - x] := by
    funext i
    fin_cases i <;> simp [p, e, f]
  calc
    LinearIndependent ℝ ![y - x, z - x] ↔
        LinearIndependent ℝ (fun i : {i : Fin 3 // i ≠ 0} => p i.1 -ᵥ p 0) :=
      linearIndependent_equiv' (e := e)
        (f := fun i : {i : Fin 3 // i ≠ 0} => p i.1 -ᵥ p 0)
        (g := ![y - x, z - x]) hfun
    _ ↔ AffineIndependent ℝ p :=
      (affineIndependent_iff_linearIndependent_vsub (k := ℝ) p 0).symm
    _ ↔ ¬ Collinear ℝ ({x, y, z} : Set (E d)) := by
      simpa [p] using (affineIndependent_iff_not_collinear_set (k := ℝ)
        (p₁ := x) (p₂ := y) (p₃ := z))

private theorem collinear_of_mem_affineSubspace_finrank_one {x y z : E 2}
    (H : AffineSubspace ℝ (E 2)) (hH : Module.finrank ℝ H.direction = 1)
    (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H) :
    Collinear ℝ ({x, y, z} : Set (E 2)) := by
  rw [collinear_iff_finrank_le_one]
  have hspan : vectorSpan ℝ ({x, y, z} : Set (E 2)) ≤ H.direction := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ
      (show x ∈ ({x, y, z} : Set (E 2)) by simp)]
    apply Submodule.span_le.2
    rintro v ⟨p, hp, rfl⟩
    have hp' : p = x ∨ p = y ∨ p = z := by simpa using hp
    rcases hp' with rfl | rfl | rfl
    · simp
    · exact AffineSubspace.vsub_mem_direction hy hx
    · exact AffineSubspace.vsub_mem_direction hz hx
  calc
    Module.finrank ℝ (vectorSpan ℝ ({x, y, z} : Set (E 2))) ≤
        Module.finrank ℝ H.direction := Submodule.finrank_mono hspan
    _ = 1 := hH

/-- A generic projection preserves the finite incidences and noncollinear triples.
CI:85–94; motions.tex:87–89. -/
theorem finite_generic_projection (d : ℕ) (X : Finset (E d)) (L : Finset (Line d)) :
    ∃ A : E d →ₗ[ℝ] E 2,
      Set.InjOn A (X : Set (E d)) ∧
      (∀ l ∈ L, Module.finrank ℝ (l.1.map A.toAffineMap).direction = 1) ∧
      (∀ l ∈ L, ∀ l' ∈ L, l.1.map A.toAffineMap = l'.1.map A.toAffineMap → l = l') ∧
      (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
        ¬ Collinear ℝ ({x, y, z} : Set (E d)) →
          ¬ Collinear ℝ ({A x, A y, A z} : Set (E 2))) := by
  classical
  let base (l : Line d) : E d := Classical.choose l.2.1
  have hbase (l : Line d) : base l ∈ l.1 := Classical.choose_spec l.2.1
  have hdirRankPos (l : Line d) : 0 < Module.finrank ℝ l.1.direction := by
    rw [l.2.2]
    omega
  let dirSubtype (l : Line d) : l.1.direction :=
    Classical.choose ((Module.finrank_pos_iff_exists_ne_zero (R := ℝ)
      (M := l.1.direction)).mp (hdirRankPos l))
  let dir (l : Line d) : E d := dirSubtype l
  have hdirMem (l : Line d) : dir l ∈ l.1.direction := (dirSubtype l).property
  have hdirNe (l : Line d) : dir l ≠ 0 :=
    fun h => Classical.choose_spec ((Module.finrank_pos_iff_exists_ne_zero (R := ℝ)
      (M := l.1.direction)).mp (hdirRankPos l)) (Subtype.ext h)
  have hpairEscape (p : {p : Line d × Line d // p ∈ L.offDiag}) :
      ∃ q : E d, q ∈ p.1.2.1 ∧ q ∉ p.1.1.1 := by
    have hp := Finset.mem_offDiag.mp p.2
    have hnotle : ¬ p.1.2.1 ≤ p.1.1.1 := by
      intro hle
      have hdle : p.1.2.1.direction ≤ p.1.1.1.direction :=
        AffineSubspace.direction_le hle
      have hd : p.1.2.1.direction = p.1.1.1.direction := by
        apply Submodule.eq_of_le_of_finrank_eq hdle
        rw [p.1.2.2.2, p.1.1.2.2]
      have heq : p.1.2.1 = p.1.1.1 :=
        AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hd p.1.2.2.1 hle
      exact hp.2.2 (Subtype.ext heq.symm)
    have hnotSub : ¬ (p.1.2.1 : Set (E d)) ⊆ p.1.1.1 := by
      intro hsub
      apply hnotle
      exact hsub
    exact Set.not_subset.mp hnotSub
  let pairWitness (p : {p : Line d × Line d // p ∈ L.offDiag}) : E d :=
    Classical.choose (hpairEscape p)
  have hpairWitness (p : {p : Line d × Line d // p ∈ L.offDiag}) :
      pairWitness p ∈ p.1.2.1 ∧ pairWitness p ∉ p.1.1.1 :=
    Classical.choose_spec (hpairEscape p)
  let endpoint (l : Line d) : E d := dir l +ᵥ base l
  let Z : Finset (E d) :=
    (((X ∪ L.image base) ∪ L.image endpoint) ∪ L.offDiag.attach.image pairWitness)
  have hXZ (x : E d) (hx : x ∈ X) : x ∈ Z := by
    simp [Z, hx]
  have hbaseZ (l : Line d) (hl : l ∈ L) : base l ∈ Z := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  have hendZ (l : Line d) (hl : l ∈ L) : endpoint l ∈ Z := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  have hpairWitnessZ (p : {p : Line d × Line d // p ∈ L.offDiag}) :
      pairWitness p ∈ Z := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨p, Finset.mem_attach L.offDiag p, rfl⟩
  let U : Finset (E d) := Z.offDiag.image (fun p => p.1 - p.2)
  let triples : Finset (E d × (E d × E d)) :=
    (Z ×ˢ (Z ×ˢ Z)).filter (fun p =>
      ¬ Collinear ℝ ({p.1, p.2.1, p.2.2} : Set (E d)))
  let P : Finset (E d × E d) := triples.image (fun p =>
    (p.2.1 - p.1, p.2.2 - p.1))
  have hU (u : E d) (hu : u ∈ U) : u ≠ 0 := by
    rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
    exact sub_ne_zero.mpr (Finset.mem_offDiag.mp hp).2.2
  have hPfirst (p : E d × E d) (hp : p ∈ P) : p.1 ∈ U := by
    rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
    have hncol := (Finset.mem_filter.mp ht).2
    have hpnts := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
    have hpnts' := Finset.mem_product.mp hpnts.2
    have hxy : t.1 ≠ t.2.1 := ne₁₂_of_not_collinear hncol
    apply Finset.mem_image.mpr
    refine ⟨(t.2.1, t.1), Finset.mem_offDiag.mpr ?_, rfl⟩
    exact ⟨hpnts'.1, hpnts.1, hxy.symm⟩
  have hPind (p : E d × E d) (hp : p ∈ P) :
    LinearIndependent ℝ ![p.1, p.2] := by
    rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
    exact (vsub_pair_independent_iff_not_collinear (d := d) (x := t.1)
      (y := t.2.1) (z := t.2.2)).2 (Finset.mem_filter.mp ht).2
  obtain ⟨A, hUmap, hPmap⟩ := generic_linear_map_for_pairs U P hU hPfirst hPind
  have hAinjZ : Set.InjOn A (Z : Set (E d)) := by
    intro x hx y hy hxy
    by_contra hne
    have hdiff : x - y ∈ U := by
      apply Finset.mem_image.mpr
      exact ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩
    exact hUmap (x - y) hdiff (by rw [map_sub, hxy, sub_self])
  have hpreserveZ : ∀ x ∈ Z, ∀ y ∈ Z, ∀ z ∈ Z,
      ¬ Collinear ℝ ({x, y, z} : Set (E d)) →
        ¬ Collinear ℝ ({A x, A y, A z} : Set (E 2)) := by
    intro x hx y hy z hz hncol hcol
    have hp : (y - x, z - x) ∈ P := by
      apply Finset.mem_image.mpr
      refine ⟨(x, (y, z)), Finset.mem_filter.mpr ?_, rfl⟩
      exact ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_product.mpr ⟨hy, hz⟩⟩, hncol⟩
    have hLI := hPmap (y - x, z - x) hp
    have hLI' : LinearIndependent ℝ ![A y - A x, A z - A x] := by
      simpa only [map_sub] using hLI
    exact (vsub_pair_independent_iff_not_collinear (d := 2) (x := A x)
      (y := A y) (z := A z)).1 hLI' hcol
  have hLineRank (l : Line d) (hl : l ∈ L) :
      Module.finrank ℝ (l.1.map A.toAffineMap).direction = 1 := by
    have hdirMap : A (dir l) ∈ (l.1.map A.toAffineMap).direction := by
      rw [AffineSubspace.map_direction]
      exact ⟨dir l, hdirMem l, rfl⟩
    have hdirMapNe : A (dir l) ≠ 0 := by
      intro hzero
      have heq : A (endpoint l) = A (base l) := by
        simp [endpoint, map_add, hzero]
      have hpoint : endpoint l = base l := hAinjZ (hendZ l hl) (hbaseZ l hl) heq
      have hz := congrArg (fun x : E d => x - base l) hpoint
      exact hdirNe l (by simpa [endpoint] using hz)
    have hle : Module.finrank ℝ (l.1.map A.toAffineMap).direction ≤ 1 := by
      rw [AffineSubspace.map_direction]
      exact (Submodule.finrank_map_le A l.1.direction).trans_eq l.2.2
    have hpos : 0 < Module.finrank ℝ (l.1.map A.toAffineMap).direction :=
      (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)
        (M := (l.1.map A.toAffineMap).direction)).2
        ⟨⟨A (dir l), hdirMap⟩, by simpa using hdirMapNe⟩
    omega
  have hLines : ∀ l ∈ L, ∀ l' ∈ L,
      l.1.map A.toAffineMap = l'.1.map A.toAffineMap → l = l' := by
    intro l hl l' hl' hmap
    by_contra hne
    have hp : (l, l') ∈ L.offDiag := Finset.mem_offDiag.mpr ⟨hl, hl', hne⟩
    let p : {p : Line d × Line d // p ∈ L.offDiag} := ⟨(l, l'), hp⟩
    let q := pairWitness p
    have hq := hpairWitness p
    have hbaseLine : base l ∈ l.1 := hbase l
    have hendLine : endpoint l ∈ l.1 := by
      exact AffineSubspace.vadd_mem_of_mem_direction (hdirMem l) hbaseLine
    have hqLine : q ∈ l'.1 := hq.1
    have hqNotLine : q ∉ l.1 := hq.2
    have hbaseNeEnd : base l ≠ endpoint l := by
      intro heq
      have hz := congrArg (fun x : E d => x - base l) heq
      exact hdirNe l (by simpa [endpoint] using hz.symm)
    have hnotcol : ¬ Collinear ℝ ({base l, endpoint l, q} : Set (E d)) := by
      intro hc
      have hqSpan := hc.mem_affineSpan_of_mem_of_ne
        (p₁ := base l) (p₂ := endpoint l) (p₃ := q)
        (by simp) (by simp) (by simp) hbaseNeEnd
      have hspanLe : line[ℝ, base l, endpoint l] ≤ l.1 :=
        affineSpan_pair_le_of_mem_of_mem hbaseLine hendLine
      exact hqNotLine (hspanLe hqSpan)
    have hnotcolImg := hpreserveZ (base l) (hbaseZ l hl) (endpoint l) (hendZ l hl)
      q (hpairWitnessZ p) hnotcol
    have hm₁ : A (base l) ∈ l.1.map A.toAffineMap :=
      AffineSubspace.mem_map_of_mem A.toAffineMap hbaseLine
    have hm₂ : A (endpoint l) ∈ l.1.map A.toAffineMap :=
      AffineSubspace.mem_map_of_mem A.toAffineMap hendLine
    have hm₃' : A q ∈ l'.1.map A.toAffineMap :=
      AffineSubspace.mem_map_of_mem A.toAffineMap hqLine
    have hm₃ : A q ∈ l.1.map A.toAffineMap := by rw [hmap]; exact hm₃'
    have hcolImg := collinear_of_mem_affineSubspace_finrank_one
      (l.1.map A.toAffineMap) (hLineRank l hl) hm₁ hm₂ hm₃
    exact hnotcolImg hcolImg
  refine ⟨A, ?_, hLineRank, hLines, ?_⟩
  · intro x hx y hy hxy
    exact hAinjZ (hXZ x hx) (hXZ y hy) hxy
  · intro x hx y hy z hz hncol
    exact hpreserveZ x (hXZ x hx) y (hXZ y hy) z (hXZ z hz) hncol

/-- K_{2,2}-free bipartite count for point-line cell incidences. -/
theorem two_point_incidence_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (α β : Type) (A : Finset α) (B : Finset β) (edges : Finset (α × β)),
      (∀ ab ∈ edges, ab.1 ∈ A ∧ ab.2 ∈ B) →
      (∀ T : Finset α, T ⊆ A → T.card = 2 →
        (B.filter (fun b => ∀ a ∈ T, (a, b) ∈ edges)).card ≤ 1) →
      (edges.card : ℝ) ≤ K * ((A.card : ℝ) * Real.sqrt B.card + B.card) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro α β A B edges hedge hK
  let N : β → Finset α := fun b => A.filter (fun a => (a, b) ∈ edges)
  let d : β → ℕ := fun b => (N b).card
  have hsumEdges : edges.card = ∑ a ∈ A, (B.filter (fun b => (a, b) ∈ edges)).card := by
    have hmap : Set.MapsTo Prod.fst (edges : Set (α × β)) A := by
      intro ab hab
      exact (hedge ab hab).1
    have hfib (a : α) :
        (edges.filter (fun ab => ab.1 = a)).card =
          (B.filter (fun b => (a, b) ∈ edges)).card := by
      apply Finset.card_bij (fun ab _ => ab.2)
      · intro ab hab
        rcases ab with ⟨a', b⟩
        simp only [Finset.mem_filter, Prod.fst] at hab
        rcases hab with ⟨hab, ha⟩
        subst a'
        have hb := hedge (a, b) hab
        simp only [Finset.mem_filter, Prod.snd, Prod.fst]
        exact ⟨hb.2, hab⟩
      · intro ab hab ab' hab' heq
        rcases ab with ⟨a₁, b₁⟩
        rcases ab' with ⟨a₂, b₂⟩
        simp only [Finset.mem_filter, Prod.fst] at hab hab'
        rcases hab with ⟨_, ha₁⟩
        rcases hab' with ⟨_, ha₂⟩
        simp only [Prod.snd] at heq
        exact Prod.ext (ha₁.trans ha₂.symm) heq
      · intro b hb
        simp only [Finset.mem_filter, Prod.fst, Prod.snd] at hb
        rcases hb with ⟨hbB, hab⟩
        exact ⟨(a, b), by simp [hab], rfl⟩
    calc
      edges.card = ∑ a ∈ A, (edges.filter (fun ab => ab.1 = a)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      _ = _ := by simp_rw [hfib]
  have hdoubleEdges :
      (∑ a ∈ A, (B.filter (fun b => (a, b) ∈ edges)).card) =
        ∑ b ∈ B, (N b).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, N] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := A) (t := B) (r := fun a b => (a, b) ∈ edges))
  have hsum : edges.card = ∑ b ∈ B, (d b) := by
    rw [hsumEdges, hdoubleEdges]
  have hpairFilter (b : β) :
      ((A.offDiag).filter (fun p => (p.1, b) ∈ edges ∧ (p.2, b) ∈ edges)).card =
        (N b).offDiag.card := by
    congr 1
    ext p
    simp [N, Finset.mem_offDiag, and_assoc, and_left_comm, and_comm]
  have hdoublePairs :
      (∑ b ∈ B,
        ((A.offDiag).filter (fun p => (p.1, b) ∈ edges ∧ (p.2, b) ∈ edges)).card) =
      ∑ p ∈ A.offDiag,
        (B.filter (fun b => (p.1, b) ∈ edges ∧ (p.2, b) ∈ edges)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := B) (t := A.offDiag)
        (r := fun b p => (p.1, b) ∈ edges ∧ (p.2, b) ∈ edges))
  have hcommon (p : α × α) (hp : p ∈ A.offDiag) :
      (B.filter (fun b => (p.1, b) ∈ edges ∧ (p.2, b) ∈ edges)).card ≤ 1 := by
    have hp' := Finset.mem_offDiag.mp hp
    let T : Finset α := {p.1, p.2}
    have hT : T ⊆ A := by
      intro a ha
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hp'.1
      · exact hp'.2.1
    have hTc : T.card = 2 := by simp [T, hp'.2.2]
    have hbound := hK T hT hTc
    apply le_trans ?_ hbound
    apply Finset.card_le_card
    intro b hb
    simp only [Finset.mem_filter] at hb ⊢
    rcases hb with ⟨hbB, h₁, h₂⟩
    refine ⟨hbB, ?_⟩
    intro a ha
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact h₁
    · exact h₂
  have hpairNat :
      (∑ b ∈ B, (N b).offDiag.card) ≤ A.offDiag.card := by
    calc
      _ = ∑ b ∈ B,
          ((A.offDiag).filter (fun p => (p.1, b) ∈ edges ∧ (p.2, b) ∈ edges)).card := by
            apply Finset.sum_congr rfl
            intro b hb
            exact (hpairFilter b).symm
      _ = ∑ p ∈ A.offDiag,
          (B.filter (fun b => (p.1, b) ∈ edges ∧ (p.2, b) ∈ edges)).card := hdoublePairs
      _ ≤ ∑ _ ∈ A.offDiag, 1 := by
            apply Finset.sum_le_sum
            intro p hp
            exact hcommon p hp
      _ = A.offDiag.card := by simp
  have hsumReal : (edges.card : ℝ) = ∑ b ∈ B, (d b : ℝ) := by
    rw [hsum, Nat.cast_sum]
  have hpairReal :
      (∑ b ∈ B, ((d b : ℝ) ^ 2 - (d b : ℝ))) ≤
        (A.card : ℝ) ^ 2 - (A.card : ℝ) := by
    have hcast :
        (∑ b ∈ B, ((N b).offDiag.card : ℝ)) ≤ (A.offDiag.card : ℝ) := by
      exact_mod_cast hpairNat
    have hcastOff (S : Finset α) :
        (S.offDiag.card : ℝ) = (S.card : ℝ) ^ 2 - S.card := by
      have hle : S.card ≤ S.card * S.card := Nat.le_mul_self _
      rw [Finset.offDiag_card, Nat.cast_sub hle]
      simp [Nat.cast_mul, pow_two]
    calc
      _ = ∑ b ∈ B, ((N b).offDiag.card : ℝ) := by
        apply Finset.sum_congr rfl
        intro b hb
        simpa only [d] using (hcastOff (N b)).symm
      _ ≤ (A.offDiag.card : ℝ) := hcast
      _ = _ := hcastOff A
  have hm : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hcs :
      (∑ b ∈ B, (d b : ℝ)) ^ 2 ≤
        (B.card : ℝ) * ∑ b ∈ B, (d b : ℝ) ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq B (fun _ : β => (1 : ℝ)) (fun b => (d b : ℝ)))
  have hsumSq :
      (∑ b ∈ B, (d b : ℝ) ^ 2) ≤ (A.card : ℝ) ^ 2 + (edges.card : ℝ) := by
    calc
      _ = (∑ b ∈ B, ((d b : ℝ) ^ 2 - (d b : ℝ))) + ∑ b ∈ B, (d b : ℝ) := by
        rw [← Finset.sum_add_distrib]
        congr 1
        ext b
        ring
      _ ≤ ((A.card : ℝ) ^ 2 - (A.card : ℝ)) + (edges.card : ℝ) := by
        exact add_le_add hpairReal (by rw [hsumReal])
      _ ≤ (A.card : ℝ) ^ 2 + (edges.card : ℝ) := by nlinarith
  have he : 0 ≤ (edges.card : ℝ) := Nat.cast_nonneg _
  have hfinal : (edges.card : ℝ) ≤ (A.card : ℝ) * Real.sqrt B.card + B.card := by
    by_contra hnot
    have hgt : (A.card : ℝ) * Real.sqrt B.card + B.card < edges.card := lt_of_not_ge hnot
    let v : ℝ := (A.card : ℝ) * Real.sqrt B.card
    have hv : 0 ≤ v := mul_nonneg hm (Real.sqrt_nonneg _)
    have hroot : (Real.sqrt (B.card : ℝ)) ^ 2 = (B.card : ℝ) := Real.sq_sqrt hn
    have hcs' : (edges.card : ℝ) ^ 2 ≤
        (B.card : ℝ) * ((A.card : ℝ) ^ 2 + (edges.card : ℝ)) := by
      calc
        (edges.card : ℝ) ^ 2 = (∑ b ∈ B, (d b : ℝ)) ^ 2 := by rw [hsumReal]
        _ ≤ (B.card : ℝ) * ∑ b ∈ B, (d b : ℝ) ^ 2 := hcs
        _ ≤ (B.card : ℝ) * ((A.card : ℝ) ^ 2 + (edges.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsumSq hn
    have hprodUpper : (edges.card : ℝ) * ((edges.card : ℝ) - B.card) ≤
        (B.card : ℝ) * (A.card : ℝ) ^ 2 := by nlinarith [hcs']
    have hEgtV : v < (edges.card : ℝ) := by
      dsimp [v] at *
      linarith [hgt, hn]
    have hGap : v < (edges.card : ℝ) - B.card := by
      dsimp [v] at *
      linarith [hgt]
    have hvSq : v ^ 2 = (B.card : ℝ) * (A.card : ℝ) ^ 2 := by
      dsimp [v]
      rw [mul_pow, hroot]
      ring
    have hprodLower : v ^ 2 <
        (edges.card : ℝ) * ((edges.card : ℝ) - B.card) := by
      by_cases hv0 : v = 0
      · have hEpos : 0 < (edges.card : ℝ) := by linarith
        have hGapPos : 0 < (edges.card : ℝ) - B.card := by linarith
        rw [hv0]
        nlinarith [mul_pos hEpos hGapPos]
      · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
        have hepos : 0 < (edges.card : ℝ) := lt_trans hvpos hEgtV
        calc
          v ^ 2 = v * v := by ring
          _ < (edges.card : ℝ) * v := mul_lt_mul_of_pos_right hEgtV hvpos
          _ < (edges.card : ℝ) * ((edges.card : ℝ) - B.card) :=
            mul_lt_mul_of_pos_left hGap hepos
    nlinarith [hprodUpper, hprodLower, hvSq]
  simpa using hfinal

theorem line_relationMass (X : Finset (E 2)) (L : Finset (Line 2)) :
    relationMass X L (fun x l => x ∈ l.1) = (incidences X L:ℝ) := by
  rw [relationMass_sum_card]
  simp [incidences,lineMultiplicity]

/-- Two distinct points determine at most one listed affine line. -/
theorem two_points_line_set_bound (U : Finset (E 2)) (hU : U.card = 2) :
    FiniteCardBound {l : Line 2 | (U:Set (E 2)) ⊆ l.1} 1 := by
  have hss : {l : Line 2 | (U:Set (E 2)) ⊆ l.1}.Subsingleton := by
    intro l hl l' hl'
    by_contra hne
    have hi := affine_lines_intersection_bound 2 l l' hne
    have hb := finset_card_le_ncard U _ hi.1 (fun x hx => ⟨hl hx,hl' hx⟩)
    have hr : (U.card:ℝ) ≤ 1 := (Nat.cast_le.mpr hb).trans hi.2
    rw [hU] at hr
    norm_num at hr
  exact ⟨hss.finite,by exact_mod_cast (Set.ncard_le_one hss.finite).mpr hss⟩

set_option maxHeartbeats 1000000 in
/-- The two-point KST count specialized to planar affine lines. -/
theorem line_cell_mass_bound : ∃ K : ℝ,0 < K ∧
    ∀ (X : Finset (E 2)) (L : Finset (Line 2)),
      relationMass X L (fun x l => x ∈ l.1) ≤ K*((X.card:ℝ)*Real.sqrt L.card+L.card) := by
  obtain ⟨K,hK,hbound⟩ := two_point_incidence_bound
  refine ⟨K,hK,?_⟩
  intro X L
  letI : DecidableEq (E 2 × Line 2) := Classical.decEq _
  let edges := relationEdges X L (fun x l => x ∈ l.1)
  rw [relationMass_edges]
  apply hbound (E 2) (Line 2) X L edges
  · intro ab hab
    exact Finset.mem_product.mp (Finset.mem_filter.mp hab).1
  · intro U hUX hU
    have hlines := two_points_line_set_bound U hU
    let B := L.filter (fun l => ∀ x ∈ U,(x,l) ∈ edges)
    have hsub : (B:Set (Line 2)) ⊆ {l : Line 2 | (U:Set (E 2)) ⊆ l.1} := by
      intro l hl x hx
      exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hl).2 x hx)).2
    have hcard := finset_card_le_ncard B _ hlines.1 hsub
    have hreal : (B.card:ℝ) ≤ 1 := (Nat.cast_le.mpr hcard).trans hlines.2
    have hn : B.card ≤ 1 := Nat.cast_le.mp (by simpa using hreal : (B.card:ℝ) ≤ (1:ℕ))
    convert hn using 1
    congr 1
    ext l
    simp only [B,Finset.mem_filter]

/-- Noncontained lines meet the polynomial boundary only at restriction roots. -/
theorem line_boundary_mass (f : Poly 2) (X : Finset (E 2)) (L : Finset (Line 2))
    (hL : ∀ l ∈ L,¬onPolynomial f l) :
    relationMass (pointsIn X (zeroSet f)) L (fun x l => x ∈ l.1) ≤
      (L.card:ℝ)*((f.totalDegree:ℝ)+1) := by
  rw [relationMass_pointsIn]
  calc
    _ ≤ ∑ _l ∈ L,((f.totalDegree:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro l hl
      let S := pointsIn X (zeroSet f ∩ (l.1:Set (E 2)))
      have hS : ∀ x ∈ S,x ∈ l.1 ∧ evalR f x = 0 := by
        intro x hx
        have hxin := (mem_pointsIn X _ x).mp hx
        exact ⟨hxin.2.2,hxin.2.1⟩
      have hn : S.card ≤ f.totalDegree := by
        by_contra hnot
        exact hL l hl (polynomial_line_zeros 2 f l S hS (by omega))
      have hnr : (S.card:ℝ) ≤ f.totalDegree := Nat.cast_le.mpr hn
      change (S.card:ℝ) ≤ (f.totalDegree:ℝ)+1
      linarith
    _ = _ := by simp;ring

theorem line_partition_construct : ∃ K : ℝ, 0 < K ∧
    ∀ (X : Finset (E 2)) (C : Finset (Line 2)) (r : ℕ), 1 ≤ r →
      (incidences X C:ℝ) ≤ K*((X.card:ℝ)*Real.sqrt C.card/Real.sqrt r+
        (C.card:ℝ)*r+X.card+(r:ℝ)^2) := by
  obtain ⟨p,hp,hpart⟩ := ci_partition_dim 2 (by norm_num)
  obtain ⟨k,hk,hcell⟩ := line_cell_mass_bound
  let D := p+1
  let H := p*Real.sqrt D*Real.sqrt p
  let K := k*H+(k+1)*D+1+p^2
  have hD : 0 < D := by dsimp [D]; linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X C r hr
  have hrone : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0:ℝ) < r := by positivity
  obtain ⟨fs,cells,hf,hdeg,hcard,hcells,hdisj,hcover,hline⟩ := hpart X r hr
  let f := fs.prod
  let C₀ := C.filter (fun c => onPolynomial f c)
  let C₁ := C.filter (fun c => ¬ onPolynomial f c)
  let a : Set (E 2) → ℝ := fun R => (pointsIn X R).card
  let b : Set (E 2) → ℝ := fun R => (C₁.filter (fun c => (R ∩ (c.1:Set (E 2))).Nonempty)).card
  have hC₁ : ∀ c ∈ C₁, ¬ onPolynomial f c := fun c hc => (Finset.mem_filter.mp hc).2
  have hC₁card : (C₁.card:ℝ) ≤ C.card := by exact_mod_cast Finset.card_filter_le C (fun c => ¬onPolynomial f c)
  have hcross : (f.totalDegree:ℝ)+1 ≤ D*r := by dsimp [D]; dsimp [f]; nlinarith
  have hsum : (∑ R ∈ cells, b R) ≤ D*(C.card:ℝ)*r := by
    have hswap := relationMass_swap cells C₁ (fun R c => (R ∩ (c.1:Set (E 2))).Nonempty)
    rw [relationMass_sum_card, relationMass_sum_card] at hswap
    have hc : (∑ R ∈ cells, b R) ≤ (C₁.card:ℝ)*((f.totalDegree:ℝ)+1) := by
      rw [show (∑ R ∈ cells,b R) = ∑ c ∈ C₁, ((cells.filter (fun R => (R ∩ (c.1:Set (E 2))).Nonempty)).card:ℝ) from hswap]
      calc
        _ ≤ ∑ _c ∈ C₁, ((f.totalDegree:ℝ)+1) := by
          apply Finset.sum_le_sum
          intro c hc
          exact_mod_cast hline c (hC₁ c hc)
        _ = _ := by simp; ring
    calc
      _ ≤ (C₁.card:ℝ)*((f.totalDegree:ℝ)+1) := hc
      _ ≤ (C.card:ℝ)*(D*r) := mul_le_mul hC₁card hcross (by positivity) (by positivity)
      _ = _ := by ring
  have hweighted : (∑ R ∈ cells, a R*Real.sqrt (b R)) ≤
      H*(X.card:ℝ)*Real.sqrt C.card/Real.sqrt r :=
    partition_sqrt_sum cells a b p D X.card C.card r hp.le hD.le (by positivity) (by positivity) hrpos
      (fun R hR => ⟨Nat.cast_nonneg _,(hcells R hR).2.2⟩)
      (fun R _ => Nat.cast_nonneg _) hcard hsum
  have hcellSum : (∑ R ∈ cells, relationMass (pointsIn X R) C₁ (fun x c => x ∈ c.1)) ≤
      k*(H*(X.card:ℝ)*Real.sqrt C.card/Real.sqrt r+D*(C.card:ℝ)*r) := by
    calc
      _ ≤ ∑ R ∈ cells, k*(a R*Real.sqrt (b R)+b R) := by
        apply Finset.sum_le_sum
        intro R hR
        rw [relationMass_restrict_right (pointsIn X R) C₁ (fun x c => x ∈ c.1)
          (fun c => (R ∩ (c.1:Set (E 2))).Nonempty) (by
            intro x hx c hc hxc
            exact ⟨x,(Finset.mem_filter.mp hx).2,hxc⟩)]
        exact hcell _ _
      _ = k*((∑ R ∈ cells,a R*Real.sqrt (b R))+(∑ R ∈ cells,b R)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hweighted hsum) hk.le
  have houtside : relationMass (pointsIn X (zeroSet f)ᶜ) C₁ (fun x c => x ∈ c.1) ≤
      k*(H*(X.card:ℝ)*Real.sqrt C.card/Real.sqrt r+D*(C.card:ℝ)*r) := by
    apply (relationMass_cover _ _ _ cells (fun R => pointsIn X R) ?_).trans hcellSum
    intro x hx
    have hxX : x ∈ X := (mem_pointsIn X _ x).mp hx |>.1
    have hxoff : x ∈ (zeroSet f)ᶜ := (mem_pointsIn X _ x).mp hx |>.2
    rw [← hcover] at hxoff
    obtain ⟨R,hR,hxR⟩ := (by simpa using hxoff : ∃ R ∈ cells,x ∈ R)
    exact ⟨R,hR,Finset.mem_filter.mpr ⟨hxX,hxR⟩⟩
  have hboundary : relationMass (pointsIn X (zeroSet f)) C₁ (fun x c => x ∈ c.1) ≤ D*(C.card:ℝ)*r := by
    calc
      _ ≤ (C₁.card:ℝ)*((f.totalDegree:ℝ)+1) := line_boundary_mass f X C₁ hC₁
      _ ≤ (C.card:ℝ)*(D*r) := mul_le_mul hC₁card hcross (by positivity) (by positivity)
      _ = _ := by ring
  have hcontained : relationMass X C₀ (fun x c => x ∈ c.1) ≤ X.card+p^2*(r:ℝ)^2 := by
    have hc := planar_contained_line_incidence f hf X C₀ (fun c hc => (Finset.mem_filter.mp hc).2)
    have hd : (f.totalDegree:ℝ)^2 ≤ p^2*(r:ℝ)^2 := by
      have hd := hdeg
      change (f.totalDegree:ℝ) ≤ p*r at hd
      nlinarith [show (0:ℝ) ≤ (f.totalDegree:ℝ) from Nat.cast_nonneg _]
    linarith
  have htotal : (incidences X C:ℝ) ≤
      k*H*((X.card:ℝ)*Real.sqrt C.card/Real.sqrt r)+
      (k+1)*D*((C.card:ℝ)*r)+(X.card:ℝ)+p^2*(r:ℝ)^2 := by
    have hsplit := relationMass_split_right X C (fun x c => x ∈ c.1) (fun c => onPolynomial f c)
    have hsplitX := relationMass_split_left X C₁ (fun x c => x ∈ c.1) (fun x => x ∈ zeroSet f)
    rw [line_relationMass] at hsplit
    change (incidences X C:ℝ) = relationMass X C₀ (fun x c => x ∈ c.1)+relationMass X C₁ (fun x c => x ∈ c.1) at hsplit
    have hcomp : X.filter (fun x => x ∉ zeroSet f) = pointsIn X (zeroSet f)ᶜ := by
      ext x; simp [pointsIn]
    rw [hcomp] at hsplitX
    change relationMass X C₁ (fun x c => x ∈ c.1) = relationMass (pointsIn X (zeroSet f)) C₁ (fun x c => x ∈ c.1)+
      relationMass (pointsIn X (zeroSet f)ᶜ) C₁ (fun x c => x ∈ c.1) at hsplitX
    calc
      _ = relationMass X C₀ (fun x c => x ∈ c.1) +
          (relationMass (pointsIn X (zeroSet f)) C₁ (fun x c => x ∈ c.1) +
           relationMass (pointsIn X (zeroSet f)ᶜ) C₁ (fun x c => x ∈ c.1)) := by
        rw [hsplit,hsplitX]
      _ ≤ ((X.card:ℝ)+p^2*(r:ℝ)^2) +
          (D*(C.card:ℝ)*r+k*(H*(X.card:ℝ)*Real.sqrt C.card/Real.sqrt r+D*(C.card:ℝ)*r)) :=
        add_le_add hcontained (add_le_add hboundary houtside)
      _ = _ := by ring
  have hnonD : 0 ≤ (k+1)*D := by positivity
  have hnonH : 0 ≤ k*H := by positivity
  have hcoeff₁ : k*H ≤ K := by dsimp [K]; nlinarith [sq_nonneg p]
  have hcoeff₂ : (k+1)*D ≤ K := by dsimp [K]; nlinarith [sq_nonneg p]
  have hcoeff₃ : (1:ℝ) ≤ K := by dsimp [K]; nlinarith [sq_nonneg p]
  have hcoeff₄ : p^2 ≤ K := by dsimp [K]; linarith
  apply htotal.trans
  calc
    _ ≤ K*((X.card:ℝ)*Real.sqrt C.card/Real.sqrt r)+
        K*((C.card:ℝ)*r)+K*(X.card:ℝ)+K*(r:ℝ)^2 := by
          gcongr
          exact le_mul_of_one_le_left (Nat.cast_nonneg _) hcoeff₃
    _ = _ := by ring

/-- Point-line estimate from planar sign partitioning, before optimizing r. -/
theorem line_partition_estimate : ∃ K : ℝ, 0 < K ∧
    ∀ (X : Finset (E 2)) (L : Finset (Line 2)) (r : ℕ), 1 ≤ r →
      (incidences X L : ℝ) ≤ K *
        ((X.card : ℝ) * Real.sqrt L.card / Real.sqrt r +
          (L.card : ℝ) * r + X.card + (r : ℝ) ^ 2) := by
  exact line_partition_construct

/-- Planar ST by partitioning; avoids the graph-drawing Euler foundation. -/
theorem ci_st_planar : ∃ C : ℝ, 0 < C ∧
    ∀ (X : Finset (E 2)) (L : Finset (Line 2)),
      (incidences X L : ℝ) ≤ C *
        ((X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          X.card + L.card) := by
  obtain ⟨K, hK, hpart⟩ := line_partition_estimate
  refine ⟨8 * K + 2, by positivity, ?_⟩
  intro X L
  by_cases hX : X.card = 0
  · have hXempty : X = ∅ := Finset.card_eq_zero.mp hX
    simp only [hXempty, incidences, Finset.sum_empty, Nat.cast_zero]
    positivity
  by_cases hL : L.card = 0
  · have hLempty : L = ∅ := Finset.card_eq_zero.mp hL
    simp only [hLempty, incidences, lineMultiplicity, Finset.filter_empty,
      Finset.card_empty, Finset.sum_const_zero, Nat.cast_zero]
    positivity
  apply line_partition_optimize K X.card L.card (incidences X L) hK
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hX)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL)
  · rw [← line_relationMass]
    exact line_pair_incidence_bound X L
  · exact hpart X L

private noncomputable def incidenceEdges {d : ℕ} (X : Finset (E d)) (L : Finset (Line d)) :
    Finset (E d × Line d) :=
  (X ×ˢ L).filter (fun p => p.1 ∈ p.2.1)

private theorem incidenceEdges_card {d : ℕ} (X : Finset (E d)) (L : Finset (Line d)) :
    (incidenceEdges X L).card = incidences X L := by
  classical
  let Q := incidenceEdges X L
  have hmap : Set.MapsTo Prod.fst (Q : Set (E d × Line d)) X := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hfib (x : E d) (hx : x ∈ X) :
      (Q.filter (fun p => p.1 = x)).card = (L.filter (fun l => x ∈ l.1)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpQ, hpx⟩
      rcases Finset.mem_filter.mp hpQ with ⟨hpProd, hpInc⟩
      have hpL := (Finset.mem_product.mp hpProd).2
      simp only [Finset.mem_filter]
      exact ⟨hpL, by simpa [hpx] using hpInc⟩
    · intro p hp p' hp' heq
      rcases Finset.mem_filter.mp hp with ⟨_, hpx⟩
      rcases Finset.mem_filter.mp hp' with ⟨_, hpx'⟩
      exact Prod.ext (hpx.trans hpx'.symm) heq
    · intro l hl
      rcases Finset.mem_filter.mp hl with ⟨hlL, hxl⟩
      refine ⟨(x, l), ?_, rfl⟩
      simp [Q, incidenceEdges, hx, hlL, hxl]
  change Q.card = incidences X L
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  unfold incidences lineMultiplicity
  apply Finset.sum_congr rfl
  intro x hx
  exact hfib x hx

/-- ci:st, specialized affine interface includes all ambient dimensions. -/
theorem ci_st : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Finset (E d)) (L : Finset (Line d)),
      (incidences X L : ℝ) ≤ C *
        ((X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          X.card + L.card) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := ci_st_planar
  refine ⟨C, hCpos, ?_⟩
  intro d X L
  obtain ⟨A, hA, hRank, hLines, hTriples⟩ := finite_generic_projection d X L
  let projectLine : {l : Line d // l ∈ L} → Line 2 := fun l =>
    ⟨l.1.1.map A.toAffineMap,
      ⟨by
        rcases l.1.2.1 with ⟨x, hx⟩
        exact ⟨A x, AffineSubspace.mem_map_of_mem A.toAffineMap hx⟩,
       hRank l.1 l.2⟩⟩
  have hprojectLineInj : Function.Injective projectLine := by
    intro l l' heq
    apply Subtype.ext
    apply hLines l.1 l.2 l'.1 l'.2
    exact congrArg Subtype.val heq
  let Xp := X.image A
  let Lp := L.attach.image projectLine
  have hXcard : Xp.card = X.card := by
    exact Finset.card_image_of_injOn hA
  have hLcard : Lp.card = L.card := by
    simp only [Lp, Finset.card_image_of_injective _ hprojectLineInj, Finset.card_attach]
  let Q := incidenceEdges X L
  let Qp := incidenceEdges Xp Lp
  have hQcard : Q.card = incidences X L := incidenceEdges_card X L
  have hQpcard : Qp.card = incidences Xp Lp := incidenceEdges_card Xp Lp
  have qmem (q : {p : E d × Line d // p ∈ Q}) :
      q.1.1 ∈ X ∧ q.1.2 ∈ L ∧ q.1.1 ∈ q.1.2.1 := by
    rcases Finset.mem_filter.mp q.2 with ⟨hprod, hinc⟩
    exact ⟨(Finset.mem_product.mp hprod).1, (Finset.mem_product.mp hprod).2, hinc⟩
  let mapEdge (q : {p : E d × Line d // p ∈ Q}) : E 2 × Line 2 :=
    (A q.1.1, projectLine ⟨q.1.2, (qmem q).2.1⟩)
  let Qimg := Q.attach.image mapEdge
  have hQimgSub : Qimg ⊆ Qp := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hq' := qmem q
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr ⟨q.1.1, hq'.1, rfl⟩,
        Finset.mem_image.mpr ⟨⟨q.1.2, hq'.2.1⟩,
          Finset.mem_attach L ⟨q.1.2, hq'.2.1⟩, rfl⟩⟩
    · exact AffineSubspace.mem_map_of_mem A.toAffineMap hq'.2.2
  have hmapEdgeInj : Function.Injective mapEdge := by
    intro q q' hqq'
    apply Subtype.ext
    apply Prod.ext
    · apply hA (qmem q).1 (qmem q').1
      exact congrArg Prod.fst hqq'
    · have hlines' :
          projectLine ⟨q.1.2, (qmem q).2.1⟩ =
            projectLine ⟨q'.1.2, (qmem q').2.1⟩ := congrArg Prod.snd hqq'
      have hsub : (⟨q.1.2, (qmem q).2.1⟩ : {l : Line d // l ∈ L}) =
          ⟨q'.1.2, (qmem q').2.1⟩ := hprojectLineInj hlines'
      exact congrArg Subtype.val hsub
  have hQimgCard : Qimg.card = Q.card := by
    change (Q.attach.image mapEdge).card = Q.card
    rw [Finset.card_image_of_injective _ hmapEdgeInj, Finset.card_attach]
  have hincNat : incidences X L ≤ incidences Xp Lp := by
    rw [← hQcard, ← hQpcard]
    calc
      Q.card = Qimg.card := hQimgCard.symm
      _ ≤ Qp.card := Finset.card_le_card hQimgSub
  have hplanar := hC Xp Lp
  calc
    (incidences X L : ℝ) ≤ (incidences Xp Lp : ℝ) := by exact_mod_cast hincNat
    _ ≤ C * ((Xp.card : ℝ) ^ ((2 : ℝ) / 3) * (Lp.card : ℝ) ^ ((2 : ℝ) / 3) +
          Xp.card + Lp.card) := hplanar
    _ = C * ((X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          X.card + L.card) := by rw [hXcard, hLcard]

/-- Rich points and rich lines, CI:56–84. -/
private noncomputable def lineThrough {d : ℕ} (x y : E d) (hxy : x ≠ y) : Line d :=
  ⟨affineSpan ℝ ({x, y} : Set (E d)),
    ⟨⟨x, left_mem_affineSpan_pair ℝ x y⟩, by
      rw [direction_affineSpan, vectorSpan_pair_rev]
      apply finrank_span_singleton
      intro hv
      exact hxy.symm (vsub_eq_zero_iff_eq.mp hv)⟩⟩

private theorem eq_of_two_mem_lines {d : ℕ} {l l' : Line d} {x y : E d}
    (hx : x ∈ l.1.1) (hx' : x ∈ l'.1.1)
    (hy : y ∈ l.1.1) (hy' : y ∈ l'.1.1) (hxy : x ≠ y) : l = l' := by
  have hv : y -ᵥ x ≠ 0 := by
    intro hz
    exact hxy.symm (vsub_eq_zero_iff_eq.mp hz)
  have hs : ℝ ∙ (y -ᵥ x) ≤ l.1.direction := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact AffineSubspace.vsub_mem_direction hy hx
  have hs' : ℝ ∙ (y -ᵥ x) ≤ l'.1.direction := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact AffineSubspace.vsub_mem_direction hy' hx'
  have hd : ℝ ∙ (y -ᵥ x) = l.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq hs
    rw [finrank_span_singleton hv, l.2.2]
  have hd' : ℝ ∙ (y -ᵥ x) = l'.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq hs'
    rw [finrank_span_singleton hv, l'.2.2]
  have hdir : l.1.direction = l'.1.direction := hd.symm.trans hd'
  have hflat : l.1 = l'.1 :=
    AffineSubspace.ext_of_direction_eq hdir ⟨x, hx, hx'⟩
  exact Subtype.ext hflat

private theorem richPoints_pair_cover {d : ℕ} (L : Finset (Line d)) (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ T : Finset (E d), richPoints L k ⊆ (T : Set (E d)) ∧ T.card ≤ L.card ^ 2 := by
  classical
  let witness : {p : Line d × Line d // p ∈ L.offDiag} → E d := fun p =>
    if h : ∃ z, z ∈ p.1.1.1 ∧ z ∈ p.1.2.1 then Classical.choose h else 0
  have hwitness (p : {p : Line d × Line d // p ∈ L.offDiag}) {z : E d}
      (hz₁ : z ∈ p.1.1.1) (hz₂ : z ∈ p.1.2.1) :
      witness p ∈ p.1.1.1 ∧ witness p ∈ p.1.2.1 := by
    dsimp [witness]
    split_ifs with h
    · exact Classical.choose_spec h
    · exact False.elim (h ⟨z, hz₁, hz₂⟩)
  let T := L.offDiag.attach.image witness
  have hTcard : T.card ≤ L.card ^ 2 := by
    dsimp [T]
    calc
      _ ≤ L.offDiag.attach.card := Finset.card_image_le
      _ = L.offDiag.card := Finset.card_attach
      _ ≤ L.card ^ 2 := by
        rw [Finset.offDiag_card]
        calc
          L.card * L.card - L.card ≤ L.card * L.card := Nat.sub_le _ _
          _ = L.card ^ 2 := by simp [pow_two]
  have hsub : richPoints L k ⊆ (T : Set (E d)) := by
    intro x hx
    have hx' : k ≤ (L.filter (fun l => x ∈ l.1)).card := by
      simpa [richPoints, lineMultiplicity] using hx
    have hcard : 2 ≤ (L.filter (fun l => x ∈ l.1)).card := hk.trans hx'
    obtain ⟨l₁, l₂, hl₁, hl₂, hne⟩ :=
      Finset.one_lt_card_iff.mp (show 1 < (L.filter (fun l => x ∈ l.1)).card by omega)
    rcases Finset.mem_filter.mp hl₁ with ⟨hl₁L, hx₁⟩
    rcases Finset.mem_filter.mp hl₂ with ⟨hl₂L, hx₂⟩
    have hp : (l₁, l₂) ∈ L.offDiag := by
      rw [Finset.mem_offDiag]
      exact ⟨hl₁L, hl₂L, hne⟩
    let p : {p : Line d × Line d // p ∈ L.offDiag} := ⟨(l₁, l₂), hp⟩
    have hw := hwitness p hx₁ hx₂
    have heq : x = witness p := by
      by_contra hnot
      have hxy : x ≠ witness p := hnot
      have hlines := eq_of_two_mem_lines hx₁ hx₂ hw.1 hw.2 hxy
      exact hne hlines
    rw [heq]
    change witness p ∈ L.offDiag.attach.image witness
    exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ p, rfl⟩
  exact ⟨T, hsub, hTcard⟩

private theorem richLines_pair_cover {d : ℕ} (X : Finset (E d)) (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ T : Finset (Line d), richLines X k ⊆ (T : Set (Line d)) ∧ T.card ≤ X.card ^ 2 := by
  classical
  let pairLine (p : {p : E d × E d // p ∈ X.offDiag}) : Line d :=
    lineThrough p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2
  let T := X.offDiag.attach.image pairLine
  have hTcard : T.card ≤ X.card ^ 2 := by
    dsimp [T]
    calc
      _ ≤ X.offDiag.attach.card := Finset.card_image_le
      _ = X.offDiag.card := Finset.card_attach
      _ ≤ X.card ^ 2 := by
        rw [Finset.offDiag_card]
        calc
          X.card * X.card - X.card ≤ X.card * X.card := Nat.sub_le _ _
          _ = X.card ^ 2 := by simp [pow_two]
  have hsub : richLines X k ⊆ (T : Set (Line d)) := by
    intro l hl
    have hl' : (k : ℝ) ≤ ((pointsOn X l).card : ℝ) := by
      simpa [richLines] using hl
    have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hcard : 2 ≤ (pointsOn X l).card := by
      exact_mod_cast (hk'.trans hl')
    obtain ⟨x, y, hxyX, hyyX, hxy⟩ :=
      Finset.one_lt_card_iff.mp (show 1 < (pointsOn X l).card by omega)
    rcases Finset.mem_filter.mp hxyX with ⟨hxX, hxl⟩
    rcases Finset.mem_filter.mp hyyX with ⟨hyX, hyl⟩
    have hp : (x, y) ∈ X.offDiag := by
      rw [Finset.mem_offDiag]
      exact ⟨hxX, hyX, hxy⟩
    let p : {p : E d × E d // p ∈ X.offDiag} := ⟨(x, y), hp⟩
    have hxPair : x ∈ (pairLine p).1 := by
      change x ∈ affineSpan ℝ ({x, y} : Set (E d))
      exact left_mem_affineSpan_pair ℝ x y
    have hyPair : y ∈ (pairLine p).1 := by
      change y ∈ affineSpan ℝ ({x, y} : Set (E d))
      exact right_mem_affineSpan_pair ℝ x y
    have hline : pairLine p = l :=
      eq_of_two_mem_lines hxPair hxl hyPair hyl hxy
    change l ∈ X.offDiag.attach.image pairLine
    rw [← hline]
    exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ p, rfl⟩
  exact ⟨T, hsub, hTcard⟩

private theorem rich_real_bound {s n k C : ℝ} (hs : 0 ≤ s) (hn : 0 ≤ n)
    (hk : 2 ≤ k) (hC : 0 < C) (hpair : s ≤ n ^ 2)
    (hinc : k * s ≤ C *
      (s ^ ((2 : ℝ) / 3) * n ^ ((2 : ℝ) / 3) + s + n)) :
    s ≤ (72 * C ^ 3 + 4 * C + 1) * (n ^ 2 / k ^ 3 + n / k) := by
  let u : ℝ := s ^ ((1 : ℝ) / 3)
  let v : ℝ := n ^ ((1 : ℝ) / 3)
  let K : ℝ := 72 * C ^ 3 + 4 * C + 1
  have hu : 0 ≤ u := Real.rpow_nonneg hs _
  have hv : 0 ≤ v := Real.rpow_nonneg hn _
  have hu3 : u ^ 3 = s := by
    dsimp [u]
    rw [← Real.rpow_natCast (s ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hs]
    norm_num [Real.rpow_one]
  have hv3 : v ^ 3 = n := by
    dsimp [v]
    rw [← Real.rpow_natCast (n ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hn]
    norm_num [Real.rpow_one]
  have hs23 : s ^ ((2 : ℝ) / 3) = u ^ 2 := by
    dsimp [u]
    rw [show (2 : ℝ) / 3 = ((1 : ℝ) / 3) * 2 by norm_num,
      Real.rpow_mul hs]
    exact Real.rpow_natCast _ 2
  have hn23 : n ^ ((2 : ℝ) / 3) = v ^ 2 := by
    dsimp [v]
    rw [show (2 : ℝ) / 3 = ((1 : ℝ) / 3) * 2 by norm_num,
      Real.rpow_mul hn]
    exact Real.rpow_natCast _ 2
  have hinc' : k * u ^ 3 ≤ C * (u ^ 2 * v ^ 2 + u ^ 3 + v ^ 3) := by
    simpa only [← hu3, ← hv3, ← hs23, ← hn23] using hinc
  have hkpos : 0 < k := by linarith
  have hfirst : 0 ≤ n ^ 2 / k ^ 3 := div_nonneg (sq_nonneg n) (by positivity)
  have hsecond : 0 ≤ n / k := div_nonneg hn hkpos.le
  have hsum : 0 ≤ n ^ 2 / k ^ 3 + n / k := add_nonneg hfirst hsecond
  have hKsmall : (2 * C) ^ 3 ≤ K := by
    dsimp [K]
    nlinarith [pow_nonneg (le_of_lt hC) 3]
  have hKlinear : 4 * C ≤ K := by
    dsimp [K]
    nlinarith [pow_nonneg (le_of_lt hC) 3]
  have hKmain : 64 * C ^ 3 ≤ K := by
    dsimp [K]
    nlinarith [pow_nonneg (le_of_lt hC) 3]
  by_cases hlow : k < 2 * C
  · have hkpow : k ^ 3 ≤ (2 * C) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (le_of_lt hlow) 3
    have hratio : 1 ≤ (2 * C) ^ 3 / k ^ 3 :=
      (le_div_iff₀ (by positivity : 0 < k ^ 3)).2 (by simpa using hkpow)
    have hscaled : n ^ 2 ≤ (2 * C) ^ 3 * (n ^ 2 / k ^ 3) := by
      calc
        n ^ 2 = n ^ 2 * 1 := by ring
        _ ≤ n ^ 2 * ((2 * C) ^ 3 / k ^ 3) :=
          mul_le_mul_of_nonneg_left hratio (sq_nonneg n)
        _ = (2 * C) ^ 3 * (n ^ 2 / k ^ 3) := by
          field_simp [ne_of_gt hkpos]
          <;> ring
    have hsmall : n ^ 2 ≤ K * (n ^ 2 / k ^ 3 + n / k) := by
      calc
        n ^ 2 ≤ (2 * C) ^ 3 * (n ^ 2 / k ^ 3) := hscaled
        _ ≤ (2 * C) ^ 3 * (n ^ 2 / k ^ 3 + n / k) :=
          mul_le_mul_of_nonneg_left (by linarith [hsecond]) (by positivity)
        _ ≤ K * (n ^ 2 / k ^ 3 + n / k) := mul_le_mul_of_nonneg_right hKsmall hsum
    simpa [K] using hpair.trans hsmall
  · have hklarge : 2 * C ≤ k := le_of_not_gt hlow
    have hhigh : k / 2 * u ^ 3 ≤ C * (u ^ 2 * v ^ 2 + v ^ 3) := by
      have hcoef : 0 ≤ k / 2 - C := by linarith
      have hu3nonneg : 0 ≤ u ^ 3 := by positivity
      have hmul := mul_nonneg hcoef hu3nonneg
      nlinarith [hinc']
    by_cases hmain : C * (u ^ 2 * v ^ 2) ≤ k / 4 * u ^ 3
    · have hlinear : k / 4 * u ^ 3 ≤ C * v ^ 3 := by nlinarith [hhigh, hmain]
      have hu3bound : u ^ 3 ≤ (4 * C * v ^ 3) / k := by
        apply (le_div_iff₀ hkpos).2
        nlinarith [hlinear]
      have hlinearTarget : 4 * C * (n / k) ≤ K * (n ^ 2 / k ^ 3 + n / k) := by
        calc
          4 * C * (n / k) ≤ 4 * C * (n ^ 2 / k ^ 3 + n / k) :=
            mul_le_mul_of_nonneg_left (by linarith [hfirst]) (by positivity)
          _ ≤ K * (n ^ 2 / k ^ 3 + n / k) := mul_le_mul_of_nonneg_right hKlinear hsum
      calc
        s = u ^ 3 := hu3.symm
        _ ≤ (4 * C * v ^ 3) / k := hu3bound
        _ = 4 * C * (n / k) := by rw [hv3]; ring
        _ ≤ K * (n ^ 2 / k ^ 3 + n / k) := hlinearTarget
    · have hbig : k / 4 * u ^ 3 < C * (u ^ 2 * v ^ 2) := lt_of_not_ge hmain
      have huPos : 0 < u := by
        by_contra hnot
        have hu0 : u = 0 := le_antisymm (le_of_not_gt hnot) hu
        rw [hu0] at hbig
        norm_num at hbig
      have hmul : u ^ 2 * (k * u) < u ^ 2 * (4 * C * v ^ 2) := by
        nlinarith [hbig]
      have hcancel : k * u < 4 * C * v ^ 2 :=
        (mul_lt_mul_iff_of_pos_left (pow_pos huPos 2)).mp hmul
      have huBound : u < (4 * C * v ^ 2) / k :=
        (lt_div_iff₀ hkpos).2 (by simpa [mul_comm] using hcancel)
      have hcube : u ^ 3 ≤ ((4 * C * v ^ 2) / k) ^ 3 :=
        pow_le_pow_left₀ hu huBound.le 3
      have hv6 : v ^ 6 = n ^ 2 := by
        calc
          v ^ 6 = v ^ (3 * 2) := by norm_num
          _ = (v ^ 3) ^ 2 := by rw [pow_mul]
          _ = n ^ 2 := by rw [hv3]
      have hpower : ((4 * C * v ^ 2) / k) ^ 3 =
          64 * C ^ 3 * (n ^ 2 / k ^ 3) := by
        rw [div_pow]
        calc
          (4 * C * v ^ 2) ^ 3 / k ^ 3 = 64 * C ^ 3 * v ^ 6 / k ^ 3 := by ring
          _ = 64 * C ^ 3 * (n ^ 2 / k ^ 3) := by rw [hv6]; ring
      have hmainTarget : 64 * C ^ 3 * (n ^ 2 / k ^ 3) ≤
          K * (n ^ 2 / k ^ 3 + n / k) := by
        calc
          64 * C ^ 3 * (n ^ 2 / k ^ 3) ≤
              64 * C ^ 3 * (n ^ 2 / k ^ 3 + n / k) :=
            mul_le_mul_of_nonneg_left (by linarith [hsecond]) (by positivity)
          _ ≤ K * (n ^ 2 / k ^ 3 + n / k) := mul_le_mul_of_nonneg_right hKmain hsum
      calc
        s = u ^ 3 := hu3.symm
        _ ≤ ((4 * C * v ^ 2) / k) ^ 3 := hcube
        _ = 64 * C ^ 3 * (n ^ 2 / k ^ 3) := hpower
        _ ≤ K * (n ^ 2 / k ^ 3 + n / k) := hmainTarget

theorem ci_st_rich : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Finset (E d)) (L : Finset (Line d)) (k : ℕ), 2 ≤ k →
      FiniteCardBound (richPoints L k)
        (C * ((L.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (L.card : ℝ) / k)) ∧
      FiniteCardBound (richLines X k)
        (C * ((X.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (X.card : ℝ) / k)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := ci_st
  refine ⟨72 * C₀ ^ 3 + 4 * C₀ + 1, by positivity, ?_⟩
  intro d X L k hk
  constructor
  · obtain ⟨T, hcover, hTcard⟩ := richPoints_pair_cover L k hk
    have hR : (richPoints L k).Finite := (Finset.finite_toSet T).subset hcover
    let R := hR.toFinset
    have hRcard : (richPoints L k).ncard = R.card := by
      simpa [R] using Set.ncard_eq_toFinset_card (richPoints L k) hR
    have hRsub : R ⊆ T := by
      intro x hx
      exact hcover (hR.mem_toFinset.mp hx)
    have hRpair : R.card ≤ L.card ^ 2 := (Finset.card_le_card hRsub).trans hTcard
    have hLowerNat : R.card * k ≤ incidences R L := by
      change R.card * k ≤ ∑ x ∈ R, lineMultiplicity L x
      calc
        R.card * k = ∑ x ∈ R, k := by simp
        _ ≤ ∑ x ∈ R, lineMultiplicity L x := by
          apply Finset.sum_le_sum
          intro x hx
          have hxR := hR.mem_toFinset.mp hx
          simpa [richPoints] using hxR
    have hLower : (R.card : ℝ) * (k : ℝ) ≤ (incidences R L : ℝ) := by
      exact_mod_cast hLowerNat
    have hpair : (R.card : ℝ) ≤ (L.card : ℝ) ^ 2 := by exact_mod_cast hRpair
    have hIncRaw := hLower.trans (hC₀ d R L)
    have hInc : (k : ℝ) * (R.card : ℝ) ≤ C₀ *
        ((R.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          R.card + L.card) := by
      simpa [mul_comm] using hIncRaw
    have hnum := rich_real_bound (s := (R.card : ℝ)) (n := (L.card : ℝ))
      (k := (k : ℝ)) (C := C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hk) hC₀pos hpair hInc
    refine ⟨hR, ?_⟩
    rw [hRcard]
    exact hnum
  · obtain ⟨T, hcover, hTcard⟩ := richLines_pair_cover X k hk
    have hR : (richLines X k).Finite := (Finset.finite_toSet T).subset hcover
    let R := hR.toFinset
    have hRcard : (richLines X k).ncard = R.card := by
      simpa [R] using Set.ncard_eq_toFinset_card (richLines X k) hR
    have hRsub : R ⊆ T := by
      intro l hl
      exact hcover (hR.mem_toFinset.mp hl)
    have hRpair : R.card ≤ X.card ^ 2 := (Finset.card_le_card hRsub).trans hTcard
    have hcount : (∑ l ∈ R, (pointsOn X l).card) = incidences X R := by
      unfold incidences lineMultiplicity
      simp only [pointsOn]
      simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := R) (t := X) (r := fun l x => x ∈ l.1))
    have hLowerNat : R.card * k ≤ incidences X R := by
      rw [← hcount]
      calc
        R.card * k = ∑ l ∈ R, k := by simp
        _ ≤ ∑ l ∈ R, (pointsOn X l).card := by
          apply Finset.sum_le_sum
          intro l hl
          have hlR := hR.mem_toFinset.mp hl
          have hl' : (k : ℝ) ≤ ((pointsOn X l).card : ℝ) := by
            simpa [richLines] using hlR
          exact_mod_cast hl'
    have hLower : (R.card : ℝ) * (k : ℝ) ≤ (incidences X R : ℝ) := by
      exact_mod_cast hLowerNat
    have hpair : (R.card : ℝ) ≤ (X.card : ℝ) ^ 2 := by exact_mod_cast hRpair
    have hIncRaw := hLower.trans (hC₀ d X R)
    have hInc : (k : ℝ) * (R.card : ℝ) ≤ C₀ *
        ((R.card : ℝ) ^ ((2 : ℝ) / 3) * (X.card : ℝ) ^ ((2 : ℝ) / 3) +
          R.card + X.card) := by
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hIncRaw
    have hnum := rich_real_bound (s := (R.card : ℝ)) (n := (X.card : ℝ))
      (k := (k : ℝ)) (C := C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hk) hC₀pos hpair hInc
    refine ⟨hR, ?_⟩
    rw [hRcard]
    exact hnum

noncomputable def projectiveIncidences (d : ℕ)
    (X : Finset (PFlat ℝ (d + 1) 1)) (L : Finset (PFlat ℝ (d + 1) 2)) : ℕ :=
  ∑ x ∈ X, (L.filter (fun l => x.1 ≤ l.1)).card

private noncomputable def projectiveCoordEquiv (d : ℕ) :
    (Fin (d + 1) → ℝ) ≃ₗ[ℝ] E (d + 1) :=
  (WithLp.linearEquiv 2 ℝ (Fin (d + 1) → ℝ)).symm

private noncomputable def projectiveEuclideanSubspace {d k : ℕ}
    (p : PFlat ℝ (d + 1) k) : Submodule ℝ (E (d + 1)) :=
  p.1.map (projectiveCoordEquiv d).toLinearMap

private theorem projectiveEuclideanSubspace_finrank {d k : ℕ}
    (p : PFlat ℝ (d + 1) k) :
    Module.finrank ℝ (projectiveEuclideanSubspace p) = k := by
  change Module.finrank ℝ (p.1.map (projectiveCoordEquiv d).toLinearMap) = k
  rw [(projectiveCoordEquiv d).finrank_map_eq p.1, p.2]

private theorem exists_independent_pair_in_submodule {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V)
    (hW : Module.finrank ℝ W = 2) :
    ∃ q : V × V, q.1 ∈ W ∧ q.2 ∈ W ∧ LinearIndependent ℝ ![q.1, q.2] := by
  letI : Module.Finite ℝ W := Module.finite_of_finrank_eq_succ (by simpa using hW)
  let b := Module.finBasisOfFinrankEq ℝ W hW
  let u : V := b 0
  let v : V := b 1
  have hker : LinearMap.ker W.subtype = ⊥ := by
    ext x
    simp
  have hLI : LinearIndependent ℝ (fun i : Fin 2 => ((b i : W) : V)) :=
    b.linearIndependent.map' W.subtype hker
  have hLI' : LinearIndependent ℝ ![u, v] := by
    convert hLI using 1
    funext i
    fin_cases i <;> rfl
  exact ⟨(u, v), (b 0).property, (b 1).property, hLI'⟩

private noncomputable def independentPairInSubmodule {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V)
    (hW : Module.finrank ℝ W = 2) : V × V :=
  Classical.choose (exists_independent_pair_in_submodule W hW)

private theorem independentPairInSubmodule_spec {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V)
    (hW : Module.finrank ℝ W = 2) :
    (independentPairInSubmodule W hW).1 ∈ W ∧
      (independentPairInSubmodule W hW).2 ∈ W ∧
      LinearIndependent ℝ ![(independentPairInSubmodule W hW).1,
        (independentPairInSubmodule W hW).2] :=
  Classical.choose_spec (exists_independent_pair_in_submodule W hW)

private noncomputable def nonzeroVectorInSubmodule {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V) [Module.Finite ℝ W]
    (hW : 0 < Module.finrank ℝ W) : V :=
  ((Classical.choose ((Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := W)).mp hW)
      : W) : V)

private theorem nonzeroVectorInSubmodule_mem {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V) [Module.Finite ℝ W]
    (hW : 0 < Module.finrank ℝ W) : nonzeroVectorInSubmodule W hW ∈ W :=
  (Classical.choose ((Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := W)).mp hW)).property

private theorem nonzeroVectorInSubmodule_ne {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V) [Module.Finite ℝ W]
    (hW : 0 < Module.finrank ℝ W) : nonzeroVectorInSubmodule W hW ≠ 0 := by
  intro hz
  exact (Classical.choose_spec
    ((Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := W)).mp hW))
    (Subtype.ext hz)

private theorem exists_dual_nonzero_on_finset {V : Type*}
    [AddCommGroup V] [Module ℝ V] (S : Finset V)
    (hS : ∀ v ∈ S, v ≠ 0) :
    ∃ f : V →ₗ[ℝ] ℝ, ∀ v ∈ S, f v ≠ 0 := by
  classical
  letI : Fintype {v : V // v ∈ S} := Fintype.ofFinset S (by simp)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) (M := V)
    (fun v : {v : V // v ∈ S} => v.1) (fun v => hS v.1 v.2)
  exact ⟨f, fun v hv => hf ⟨v, hv⟩⟩

private theorem independent_pair_of_nonzero_smul {V : Type*}
    [AddCommGroup V] [Module ℝ V] {u v : V} (huv : LinearIndependent ℝ ![u, v])
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℝ ![a • u, b • v] := by
  rw [LinearIndependent.pair_smul_smul_iff (Ne.isUnit ha) (Ne.isUnit hb)]
  exact huv

private theorem normalized_mem_affineSpan_pair {V : Type*}
    [AddCommGroup V] [Module ℝ V] (f : V →ₗ[ℝ] ℝ) {u v z : V}
    (hu : f u ≠ 0) (hv : f v ≠ 0) (hz : f z ≠ 0)
    (hspan : ∃ a b : ℝ, a • u + b • v = z) :
    (f z)⁻¹ • z ∈ affineSpan ℝ
      ({(f u)⁻¹ • u, (f v)⁻¹ • v} : Set V) := by
  rcases hspan with ⟨a, b, hab⟩
  have hfz : f z = a * f u + b * f v := by
    rw [← hab]
    simp [smul_eq_mul]
  let t : ℝ := (b * f v) / f z
  have ht : 1 - t = (a * f u) / f z := by
    dsimp [t]
    field_simp [hz]
    rw [hfz]
    ring
  have hcoeff₁ : (1 - t) * (f u)⁻¹ = a * (f z)⁻¹ := by
    rw [ht]
    field_simp [hu, hz]
  have hcoeff₂ : t * (f v)⁻¹ = b * (f z)⁻¹ := by
    dsimp [t]
    field_simp [hv, hz]
  let q₀ := (f u)⁻¹ • u
  let q₁ := (f v)⁻¹ • v
  have hline : AffineMap.lineMap q₀ q₁ t = (f z)⁻¹ • z := by
    rw [AffineMap.lineMap_apply_module]
    calc
      (1 - t) • q₀ + t • q₁ =
          ((1 - t) * (f u)⁻¹) • u + (t * (f v)⁻¹) • v := by
            simp [q₀, q₁, smul_smul]
      _ = (a * (f z)⁻¹) • u + (b * (f z)⁻¹) • v := by rw [hcoeff₁, hcoeff₂]
      _ = (f z)⁻¹ • (a • u + b • v) := by
        rw [smul_add]
        congr 1 <;> rw [smul_smul] <;> ring
      _ = (f z)⁻¹ • z := by rw [hab]
  exact (mem_affineSpan_pair_iff_exists_lineMap_eq).2 ⟨t, hline⟩

private noncomputable def projectiveIncidenceEdges {d : ℕ}
    (X : Finset (PFlat ℝ (d + 1) 1)) (L : Finset (PFlat ℝ (d + 1) 2)) :
    Finset (PFlat ℝ (d + 1) 1 × PFlat ℝ (d + 1) 2) :=
  (X ×ˢ L).filter (fun p => p.1.1 ≤ p.2.1)

private theorem projectiveIncidenceEdges_card (d : ℕ)
    (X : Finset (PFlat ℝ (d + 1) 1)) (L : Finset (PFlat ℝ (d + 1) 2)) :
    (projectiveIncidenceEdges X L).card = projectiveIncidences d X L := by
  classical
  let Q := projectiveIncidenceEdges X L
  have hmap : Set.MapsTo Prod.fst (Q : Set
      (PFlat ℝ (d + 1) 1 × PFlat ℝ (d + 1) 2)) X := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hfib (x : PFlat ℝ (d + 1) 1) (hx : x ∈ X) :
      (Q.filter (fun p => p.1 = x)).card =
        (L.filter (fun l => x.1 ≤ l.1)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      rcases p with ⟨x', l⟩
      rcases Finset.mem_filter.mp hp with ⟨hpQ, hpx⟩
      rcases Finset.mem_filter.mp hpQ with ⟨hpProd, hinc⟩
      have hl : l ∈ L := (Finset.mem_product.mp hpProd).2
      change x' = x at hpx
      subst x'
      simp only [Finset.mem_filter]
      exact ⟨hl, hinc⟩
    · intro p hp p' hp' heq
      rcases p with ⟨x₁, l₁⟩
      rcases p' with ⟨x₂, l₂⟩
      rcases Finset.mem_filter.mp hp with ⟨_, hx₁⟩
      rcases Finset.mem_filter.mp hp' with ⟨_, hx₂⟩
      simp only at heq
      exact Prod.ext (hx₁.trans hx₂.symm) heq
    · intro l hl
      rcases Finset.mem_filter.mp hl with ⟨hlL, hinc⟩
      refine ⟨(x, l), ?_, rfl⟩
      simp [Q, projectiveIncidenceEdges, hx, hlL, hinc]
  calc
    Q.card = ∑ x ∈ X, (Q.filter (fun p => p.1 = x)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ x ∈ X, (L.filter (fun l => x.1 ≤ l.1)).card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hfib x hx
    _ = projectiveIncidences d X L := by rfl

/-- The projective form of ci:st, CI:61–62, 90–94. -/
theorem ci_st_projective : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Finset (PFlat ℝ (d + 1) 1))
      (L : Finset (PFlat ℝ (d + 1) 2)),
      (projectiveIncidences d X L : ℝ) ≤ C *
        ((X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          X.card + L.card) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := ci_st
  refine ⟨C, hCpos, ?_⟩
  intro d X L
  let pointRankPos (p : PFlat ℝ (d + 1) 1) :
      0 < Module.finrank ℝ (projectiveEuclideanSubspace p) := by
    rw [projectiveEuclideanSubspace_finrank]
    omega
  let pointRep (p : PFlat ℝ (d + 1) 1) : E (d + 1) :=
    nonzeroVectorInSubmodule (projectiveEuclideanSubspace p) (pointRankPos p)
  have hpointRepMem (p : PFlat ℝ (d + 1) 1) :
      pointRep p ∈ projectiveEuclideanSubspace p := by
    exact nonzeroVectorInSubmodule_mem _ _
  have hpointRepNe (p : PFlat ℝ (d + 1) 1) : pointRep p ≠ 0 := by
    exact nonzeroVectorInSubmodule_ne _ _
  let lineRank (l : PFlat ℝ (d + 1) 2) :
      Module.finrank ℝ (projectiveEuclideanSubspace l) = 2 := by
    rw [projectiveEuclideanSubspace_finrank]
  let linePair (l : PFlat ℝ (d + 1) 2) : E (d + 1) × E (d + 1) :=
    independentPairInSubmodule (projectiveEuclideanSubspace l) (lineRank l)
  let lineVec₀ (l : PFlat ℝ (d + 1) 2) : E (d + 1) := (linePair l).1
  let lineVec₁ (l : PFlat ℝ (d + 1) 2) : E (d + 1) := (linePair l).2
  have hlinePairSpec (l : PFlat ℝ (d + 1) 2) :
      lineVec₀ l ∈ projectiveEuclideanSubspace l ∧
        lineVec₁ l ∈ projectiveEuclideanSubspace l ∧
        LinearIndependent ℝ ![lineVec₀ l, lineVec₁ l] := by
    simpa [lineVec₀, lineVec₁, linePair] using
      independentPairInSubmodule_spec (projectiveEuclideanSubspace l) (lineRank l)
  have hlineVecLI (l : PFlat ℝ (d + 1) 2) :
      LinearIndependent ℝ ![lineVec₀ l, lineVec₁ l] := (hlinePairSpec l).2.2
  let U : Finset (E (d + 1)) :=
    X.attach.image (fun p => pointRep p.1) ∪
      (L.attach.image (fun l => lineVec₀ l.1) ∪ L.attach.image (fun l => lineVec₁ l.1))
  have hU : ∀ z ∈ U, z ≠ 0 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hp | hl
    · rcases Finset.mem_image.mp hp with ⟨p, hp, rfl⟩
      exact hpointRepNe p.1
    · rcases Finset.mem_union.mp hl with hl₀ | hl₁
      · rcases Finset.mem_image.mp hl₀ with ⟨l, hl, rfl⟩
        simpa using (hlineVecLI l.1).ne_zero 0
      · rcases Finset.mem_image.mp hl₁ with ⟨l, hl, rfl⟩
        simpa using (hlineVecLI l.1).ne_zero 1
  obtain ⟨f, hf⟩ := exists_dual_nonzero_on_finset U hU
  have hUPoint (p : PFlat ℝ (d + 1) 1) (hp : p ∈ X) : pointRep p ∈ U := by
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
  have hULine₀ (l : PFlat ℝ (d + 1) 2) (hl : l ∈ L) : lineVec₀ l ∈ U := by
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨⟨l, hl⟩, Finset.mem_attach _ _, rfl⟩
  have hULine₁ (l : PFlat ℝ (d + 1) 2) (hl : l ∈ L) : lineVec₁ l ∈ U := by
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨⟨l, hl⟩, Finset.mem_attach _ _, rfl⟩
  have hfPoint (p : PFlat ℝ (d + 1) 1) (hp : p ∈ X) : f (pointRep p) ≠ 0 :=
    hf _ (hUPoint p hp)
  have hfLine₀ (l : PFlat ℝ (d + 1) 2) (hl : l ∈ L) : f (lineVec₀ l) ≠ 0 :=
    hf _ (hULine₀ l hl)
  have hfLine₁ (l : PFlat ℝ (d + 1) 2) (hl : l ∈ L) : f (lineVec₁ l) ≠ 0 :=
    hf _ (hULine₁ l hl)
  let normalized (z : E (d + 1)) : E (d + 1) := (f z)⁻¹ • z
  let pointChart (p : {p : PFlat ℝ (d + 1) 1 // p ∈ X}) : E (d + 1) :=
    normalized (pointRep p.1)
  let lineChart₀ (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) : E (d + 1) :=
    normalized (lineVec₀ l.1)
  let lineChart₁ (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) : E (d + 1) :=
    normalized (lineVec₁ l.1)
  have hchartPairLI (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) :
      LinearIndependent ℝ ![lineChart₀ l, lineChart₁ l] := by
    apply independent_pair_of_nonzero_smul (hlineVecLI l.1)
    · exact inv_ne_zero (hfLine₀ l.1 l.2)
    · exact inv_ne_zero (hfLine₁ l.1 l.2)
  have hchartPairNe (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) :
      lineChart₀ l ≠ lineChart₁ l := by
    intro heq
    have hzero : (1 : ℝ) • lineChart₀ l + (-1 : ℝ) • lineChart₁ l = 0 := by
      simp [heq]
    have hcoeff := (LinearIndependent.pair_iff.mp (hchartPairLI l)) 1 (-1) hzero
    norm_num at hcoeff
  let lineChart (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) : Line (d + 1) :=
    lineThrough (lineChart₀ l) (lineChart₁ l) (hchartPairNe l)
  have hpointChartNe (p : {p : PFlat ℝ (d + 1) 1 // p ∈ X}) : pointChart p ≠ 0 := by
    dsimp [pointChart, normalized]
    exact smul_ne_zero (inv_ne_zero (hfPoint p.1 p.2)) (hpointRepNe p.1)
  have hpointChartMem (p : {p : PFlat ℝ (d + 1) 1 // p ∈ X}) :
      pointChart p ∈ projectiveEuclideanSubspace p.1 := by
    change (f (pointRep p.1))⁻¹ • pointRep p.1 ∈ projectiveEuclideanSubspace p.1
    exact (projectiveEuclideanSubspace p.1).smul_mem _ (hpointRepMem p.1)
  have hpointChartSpan (p : {p : PFlat ℝ (d + 1) 1 // p ∈ X}) :
      ℝ ∙ pointChart p = projectiveEuclideanSubspace p.1 := by
    have hle : ℝ ∙ pointChart p ≤ projectiveEuclideanSubspace p.1 := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hpointChartMem p
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_singleton (hpointChartNe p), projectiveEuclideanSubspace_finrank]
  have hlineChartSpan (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) :
      Submodule.span ℝ ({lineChart₀ l, lineChart₁ l} : Set (E (d + 1))) =
        projectiveEuclideanSubspace l.1 := by
    have hmem₀ : lineChart₀ l ∈ projectiveEuclideanSubspace l.1 := by
      change (f (lineVec₀ l.1))⁻¹ • lineVec₀ l.1 ∈ projectiveEuclideanSubspace l.1
      exact (projectiveEuclideanSubspace l.1).smul_mem _ (hlinePairSpec l.1).1
    have hmem₁ : lineChart₁ l ∈ projectiveEuclideanSubspace l.1 := by
      change (f (lineVec₁ l.1))⁻¹ • lineVec₁ l.1 ∈ projectiveEuclideanSubspace l.1
      exact (projectiveEuclideanSubspace l.1).smul_mem _ (hlinePairSpec l.1).2.1
    have hle : Submodule.span ℝ ({lineChart₀ l, lineChart₁ l} : Set (E (d + 1))) ≤
        projectiveEuclideanSubspace l.1 := by
      apply Submodule.span_le.2
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hmem₀
      · exact hmem₁
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [projectiveEuclideanSubspace_finrank,
      ← Matrix.range_cons_cons_empty (lineChart₀ l) (lineChart₁ l) ![]]
    simp [finrank_span_eq_card (hchartPairLI l)]
  have hlineChart_le_subspace (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) :
      (lineChart l).1 ≤
        (projectiveEuclideanSubspace l.1 : AffineSubspace ℝ (E (d + 1))) := by
    change affineSpan ℝ ({lineChart₀ l, lineChart₁ l} : Set (E (d + 1)) ) ≤ _
    exact affineSpan_pair_le_of_mem_of_mem
      (by change lineChart₀ l ∈ projectiveEuclideanSubspace l.1; exact
        (projectiveEuclideanSubspace l.1).smul_mem _ (hlinePairSpec l.1).1)
      (by change lineChart₁ l ∈ projectiveEuclideanSubspace l.1; exact
        (projectiveEuclideanSubspace l.1).smul_mem _ (hlinePairSpec l.1).2.1)
  have hpointChart_injective : Function.Injective pointChart := by
    intro p p' heq
    apply Subtype.ext
    apply Subtype.ext
    have hspan : ℝ ∙ pointChart p = ℝ ∙ pointChart p' := congrArg (fun z => ℝ ∙ z) heq
    rw [hpointChartSpan p, hpointChartSpan p'] at hspan
    exact Submodule.map_injective_of_injective (projectiveCoordEquiv d).injective hspan
  have hlineChart_injective : Function.Injective lineChart := by
    intro l l' heq
    apply Subtype.ext
    apply Subtype.ext
    have hq₀ : lineChart₀ l ∈ (lineChart l').1 := by
      rw [← heq]
      change lineChart₀ l ∈ affineSpan ℝ
        ({lineChart₀ l, lineChart₁ l} : Set (E (d + 1)))
      exact left_mem_affineSpan_pair ℝ (lineChart₀ l) (lineChart₁ l)
    have hq₁ : lineChart₁ l ∈ (lineChart l').1 := by
      rw [← heq]
      change lineChart₁ l ∈ affineSpan ℝ
        ({lineChart₀ l, lineChart₁ l} : Set (E (d + 1)))
      exact right_mem_affineSpan_pair ℝ (lineChart₀ l) (lineChart₁ l)
    have hq₀' : lineChart₀ l ∈ projectiveEuclideanSubspace l'.1 := by
      exact hlineChart_le_subspace l' hq₀
    have hq₁' : lineChart₁ l ∈ projectiveEuclideanSubspace l'.1 := by
      exact hlineChart_le_subspace l' hq₁
    have hWle : projectiveEuclideanSubspace l.1 ≤ projectiveEuclideanSubspace l'.1 := by
      rw [← hlineChartSpan l]
      apply Submodule.span_le.2
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hq₀'
      · exact hq₁'
    have hW : projectiveEuclideanSubspace l.1 = projectiveEuclideanSubspace l'.1 := by
      apply Submodule.eq_of_le_of_finrank_eq hWle
      rw [projectiveEuclideanSubspace_finrank, projectiveEuclideanSubspace_finrank]
    exact Submodule.map_injective_of_injective (projectiveCoordEquiv d).injective hW
  have hchartIncidence (p : {p : PFlat ℝ (d + 1) 1 // p ∈ X})
      (l : {l : PFlat ℝ (d + 1) 2 // l ∈ L}) (hpl : p.1.1 ≤ l.1.1) :
      pointChart p ∈ (lineChart l).1 := by
    have hWle : projectiveEuclideanSubspace p.1 ≤ projectiveEuclideanSubspace l.1 :=
      Submodule.map_mono hpl
    have hpointInLine : pointChart p ∈ projectiveEuclideanSubspace l.1 :=
      hWle (hpointChartMem p)
    have hspan : pointChart p ∈
        Submodule.span ℝ ({lineChart₀ l, lineChart₁ l} : Set (E (d + 1))) := by
      rw [hlineChartSpan l]
      exact hpointInLine
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
    have hfchart₀ : f (lineChart₀ l) = 1 := by
      dsimp [lineChart₀, normalized]
      simp [map_smul, smul_eq_mul, inv_mul_cancel₀ (hfLine₀ l.1 l.2)]
    have hfchart₁ : f (lineChart₁ l) = 1 := by
      dsimp [lineChart₁, normalized]
      simp [map_smul, smul_eq_mul, inv_mul_cancel₀ (hfLine₁ l.1 l.2)]
    have hfpoint : f (pointChart p) = 1 := by
      dsimp [pointChart, normalized]
      simp [map_smul, smul_eq_mul, inv_mul_cancel₀ (hfPoint p.1 p.2)]
    have hnormalized := normalized_mem_affineSpan_pair f
      (by rw [hfchart₀]; norm_num) (by rw [hfchart₁]; norm_num)
      (by rw [hfpoint]; norm_num) ⟨a, b, hab⟩
    change pointChart p ∈ affineSpan ℝ
      ({lineChart₀ l, lineChart₁ l} : Set (E (d + 1)))
    simpa [hfpoint, hfchart₀, hfchart₁] using hnormalized
  let Xp := X.attach.image pointChart
  let Lp := L.attach.image lineChart
  have hXcard : Xp.card = X.card := by
    dsimp [Xp]
    rw [Finset.card_image_of_injective _ hpointChart_injective, Finset.card_attach]
  have hLcard : Lp.card = L.card := by
    dsimp [Lp]
    rw [Finset.card_image_of_injective _ hlineChart_injective, Finset.card_attach]
  let Q := projectiveIncidenceEdges X L
  let Qp := incidenceEdges Xp Lp
  have qmem (q : {p : PFlat ℝ (d + 1) 1 × PFlat ℝ (d + 1) 2 // p ∈ Q}) :
      q.1.1 ∈ X ∧ q.1.2 ∈ L ∧ q.1.1.1 ≤ q.1.2.1 := by
    rcases Finset.mem_filter.mp q.2 with ⟨hprod, hinc⟩
    exact ⟨(Finset.mem_product.mp hprod).1, (Finset.mem_product.mp hprod).2, hinc⟩
  let mapEdge (q : {p : PFlat ℝ (d + 1) 1 × PFlat ℝ (d + 1) 2 // p ∈ Q}) :
      E (d + 1) × Line (d + 1) :=
    (pointChart ⟨q.1.1, (qmem q).1⟩, lineChart ⟨q.1.2, (qmem q).2.1⟩)
  have hmapEdgeInj : Function.Injective mapEdge := by
    intro q q' h
    apply Subtype.ext
    apply Prod.ext
    · have hp : pointChart ⟨q.1.1, (qmem q).1⟩ = pointChart ⟨q'.1.1, (qmem q').1⟩ :=
        congrArg Prod.fst h
      exact congrArg Subtype.val (hpointChart_injective hp)
    · have hl : lineChart ⟨q.1.2, (qmem q).2.1⟩ = lineChart ⟨q'.1.2, (qmem q').2.1⟩ :=
        congrArg Prod.snd h
      exact congrArg Subtype.val (hlineChart_injective hl)
  let Qimg := Q.attach.image mapEdge
  have hQimgSub : Qimg ⊆ Qp := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hq' := qmem q
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr
          ⟨⟨q.1.1, hq'.1⟩, Finset.mem_attach _ _, rfl⟩,
        Finset.mem_image.mpr ⟨⟨q.1.2, hq'.2.1⟩, Finset.mem_attach _ _, rfl⟩⟩
    · exact hchartIncidence ⟨q.1.1, hq'.1⟩ ⟨q.1.2, hq'.2.1⟩ hq'.2.2
  have hQimgCard : Qimg.card = Q.card := by
    change (Q.attach.image mapEdge).card = Q.card
    rw [Finset.card_image_of_injective _ hmapEdgeInj, Finset.card_attach]
  have hQcard : Q.card = projectiveIncidences d X L := by
    simpa [Q] using projectiveIncidenceEdges_card d X L
  have hQpcard : Qp.card = incidences Xp Lp := incidenceEdges_card Xp Lp
  have hIncNat : projectiveIncidences d X L ≤ incidences Xp Lp := by
    rw [← hQcard, ← hQpcard]
    calc
      Q.card = Qimg.card := hQimgCard.symm
      _ ≤ Qp.card := Finset.card_le_card hQimgSub
  have hIncReal : (projectiveIncidences d X L : ℝ) ≤ (incidences Xp Lp : ℝ) := by
    exact_mod_cast hIncNat
  have hPlanar := hC (d + 1) Xp Lp
  calc
    (projectiveIncidences d X L : ℝ) ≤ (incidences Xp Lp : ℝ) := hIncReal
    _ ≤ C * ((Xp.card : ℝ) ^ ((2 : ℝ) / 3) * (Lp.card : ℝ) ^ ((2 : ℝ) / 3) +
          Xp.card + Lp.card) := hPlanar
    _ = C * ((X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          X.card + L.card) := by rw [hXcard, hLcard]

private noncomputable def projectivePointRepresentative {n : ℕ}
    (p : PFlat ℝ n 1) : Fin n → ℝ :=
  nonzeroVectorInSubmodule p.1 (by rw [p.2]; omega)

private theorem projectivePointRepresentative_mem {n : ℕ}
    (p : PFlat ℝ n 1) : projectivePointRepresentative p ∈ p.1 :=
  nonzeroVectorInSubmodule_mem _ _

private theorem projectivePointRepresentative_ne {n : ℕ}
    (p : PFlat ℝ n 1) : projectivePointRepresentative p ≠ 0 :=
  nonzeroVectorInSubmodule_ne _ _

private theorem projectivePointRepresentative_span {n : ℕ}
    (p : PFlat ℝ n 1) : ℝ ∙ projectivePointRepresentative p = p.1 := by
  have hle : ℝ ∙ projectivePointRepresentative p ≤ p.1 := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact projectivePointRepresentative_mem p
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_singleton (projectivePointRepresentative_ne p), p.2]

private theorem projectivePoint_eq_of_le {n : ℕ} {p q : PFlat ℝ n 1}
    (hpq : p.1 ≤ q.1) : p = q := by
  have hsub : p.1 = q.1 :=
    Submodule.eq_of_le_of_finrank_eq hpq (by rw [p.2, q.2])
  exact Subtype.ext hsub

private theorem projective_points_independent {n : ℕ} {p q : PFlat ℝ n 1}
    (hpq : p ≠ q) :
    LinearIndependent ℝ ![projectivePointRepresentative p,
      projectivePointRepresentative q] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := by
      by_contra hb
      have hne := smul_ne_zero hb (projectivePointRepresentative_ne q)
      have hzero : b • projectivePointRepresentative q = 0 := by simpa using hab
      exact hne hzero
    exact ⟨rfl, hb⟩
  · have hsum : a • projectivePointRepresentative p =
        -(b • projectivePointRepresentative q) := eq_neg_iff_add_eq_zero.mpr hab
    have hpInQ : projectivePointRepresentative p ∈ q.1 := by
      have hmem : a • projectivePointRepresentative p ∈ q.1 := by
        rw [hsum]
        exact q.1.neg_mem (q.1.smul_mem b (projectivePointRepresentative_mem q))
      have := q.1.smul_mem a⁻¹ hmem
      simpa [smul_smul, ha] using this
    have hle : p.1 ≤ q.1 := by
      rw [← projectivePointRepresentative_span p]
      rw [Submodule.span_singleton_le_iff_mem]
      exact hpInQ
    exact False.elim (hpq (projectivePoint_eq_of_le hle))

private noncomputable def projectiveLineThroughPoints {n : ℕ}
    (p q : PFlat ℝ n 1) (hpq : p ≠ q) : PFlat ℝ n 2 := by
  let u := projectivePointRepresentative p
  let v := projectivePointRepresentative q
  have hLI : LinearIndependent ℝ ![u, v] := by
    simpa [u, v] using projective_points_independent hpq
  refine ⟨Submodule.span ℝ ({u, v} : Set (Fin n → ℝ)), ?_⟩
  rw [← Matrix.range_cons_cons_empty u v ![]]
  simp [finrank_span_eq_card hLI]

private theorem projectiveLineThroughPoints_contains_left {n : ℕ}
    (p q : PFlat ℝ n 1) (hpq : p ≠ q) :
    p.1 ≤ (projectiveLineThroughPoints p q hpq).1 := by
  change p.1 ≤ Submodule.span ℝ
    ({projectivePointRepresentative p, projectivePointRepresentative q} : Set (Fin n → ℝ))
  rw [← projectivePointRepresentative_span p]
  rw [Submodule.span_singleton_le_iff_mem]
  exact Submodule.subset_span (by simp)

private theorem projectiveLineThroughPoints_contains_right {n : ℕ}
    (p q : PFlat ℝ n 1) (hpq : p ≠ q) :
    q.1 ≤ (projectiveLineThroughPoints p q hpq).1 := by
  change q.1 ≤ Submodule.span ℝ
    ({projectivePointRepresentative p, projectivePointRepresentative q} : Set (Fin n → ℝ))
  rw [← projectivePointRepresentative_span q]
  rw [Submodule.span_singleton_le_iff_mem]
  exact Submodule.subset_span (by simp)

private theorem projectiveLineThroughPoints_eq_of_contains {n : ℕ}
    (p q : PFlat ℝ n 1) (hpq : p ≠ q) (l : PFlat ℝ n 2)
    (hp : p.1 ≤ l.1) (hq : q.1 ≤ l.1) :
    projectiveLineThroughPoints p q hpq = l := by
  have hle : (projectiveLineThroughPoints p q hpq).1 ≤ l.1 := by
    apply Submodule.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hp (projectivePointRepresentative_mem p)
    · exact hq (projectivePointRepresentative_mem q)
  have heq : (projectiveLineThroughPoints p q hpq).1 = l.1 :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [(projectiveLineThroughPoints p q hpq).2, l.2])
  exact Subtype.ext heq

private noncomputable def projectivePointOnLine {n : ℕ}
    (l : PFlat ℝ n 2) : PFlat ℝ n 1 :=
  ⟨ℝ ∙ nonzeroVectorInSubmodule l.1 (by rw [l.2]; omega),
    finrank_span_singleton (nonzeroVectorInSubmodule_ne l.1 (by rw [l.2]; omega))⟩

private theorem projectivePointOnLine_le {n : ℕ} (l : PFlat ℝ n 2) :
    (projectivePointOnLine l).1 ≤ l.1 := by
  change ℝ ∙ nonzeroVectorInSubmodule l.1 (by rw [l.2]; omega) ≤ l.1
  rw [Submodule.span_singleton_le_iff_mem]
  exact nonzeroVectorInSubmodule_mem _ _

private theorem projectivePoint_eq_of_two_lines {n : ℕ}
    {p q : PFlat ℝ n 1} {l l' : PFlat ℝ n 2}
    (hll' : l ≠ l') (hp : p.1 ≤ l.1) (hp' : p.1 ≤ l'.1)
    (hq : q.1 ≤ l.1) (hq' : q.1 ≤ l'.1) : p = q := by
  let W := l.1 ⊓ l'.1
  have hpW : p.1 ≤ W := le_inf hp hp'
  have hqW : q.1 ≤ W := le_inf hq hq'
  have hWle : W ≤ l.1 := inf_le_left
  have hWle' : W ≤ l'.1 := inf_le_right
  have hWrank : Module.finrank ℝ W = 1 := by
    have hpWrank : 1 ≤ Module.finrank ℝ W := by
      have h := Submodule.finrank_mono hpW
      rw [p.2] at h
      exact h
    have hWrankle : Module.finrank ℝ W ≤ 2 := by
      have h := Submodule.finrank_mono hWle
      rw [l.2] at h
      exact h
    by_contra hne
    have htwo : 2 ≤ Module.finrank ℝ W := by omega
    have hWl : W = l.1 :=
      Submodule.eq_of_le_of_finrank_eq hWle (by rw [l.2]; omega)
    have hWl' : W = l'.1 :=
      Submodule.eq_of_le_of_finrank_eq hWle' (by rw [l'.2]; omega)
    exact hll' (Subtype.ext (hWl.symm.trans hWl'))
  have hpEq : p.1 = W := Submodule.eq_of_le_of_finrank_eq hpW (by rw [p.2, hWrank])
  have hqEq : q.1 = W := Submodule.eq_of_le_of_finrank_eq hqW (by rw [q.2, hWrank])
  exact Subtype.ext (hpEq.trans hqEq.symm)

private theorem projective_rich_points_pair_cover {d : ℕ}
    (L : Finset (PFlat ℝ (d + 1) 2)) (k : ℕ) (hk : 2 ≤ k) :
    ∃ T : Finset (PFlat ℝ (d + 1) 1),
      {x : PFlat ℝ (d + 1) 1 | k ≤ (L.filter (fun l => x.1 ≤ l.1)).card} ⊆
        (T : Set (PFlat ℝ (d + 1) 1)) ∧
        T.card ≤ L.card ^ 2 := by
  classical
  let witness (p : {p : PFlat ℝ (d + 1) 2 × PFlat ℝ (d + 1) 2 // p ∈ L.offDiag}) :=
    if h : ∃ x : PFlat ℝ (d + 1) 1, x.1 ≤ p.1.1.1 ∧ x.1 ≤ p.1.2.1 then
      Classical.choose h
    else projectivePointOnLine p.1.1
  let T := L.offDiag.attach.image witness
  have hTcard : T.card ≤ L.card ^ 2 := by
    dsimp [T]
    calc
      _ ≤ L.offDiag.attach.card := Finset.card_image_le
      _ = L.offDiag.card := Finset.card_attach
      _ ≤ L.card ^ 2 := by
        rw [Finset.offDiag_card]
        calc
          L.card * L.card - L.card ≤ L.card * L.card := Nat.sub_le _ _
          _ = L.card ^ 2 := by simp [pow_two]
  have hsub : {x : PFlat ℝ (d + 1) 1 | k ≤ (L.filter (fun l => x.1 ≤ l.1)).card} ⊆
      (T : Set (PFlat ℝ (d + 1) 1)) := by
    intro x hx
    have hcard : 2 ≤ (L.filter (fun l => x.1 ≤ l.1)).card := hk.trans hx
    obtain ⟨l₁, l₂, hl₁, hl₂, hne⟩ :=
      Finset.one_lt_card_iff.mp (show 1 < (L.filter (fun l => x.1 ≤ l.1)).card by omega)
    rcases Finset.mem_filter.mp hl₁ with ⟨hl₁L, hx₁⟩
    rcases Finset.mem_filter.mp hl₂ with ⟨hl₂L, hx₂⟩
    have hp : (l₁, l₂) ∈ L.offDiag := by
      rw [Finset.mem_offDiag]
      exact ⟨hl₁L, hl₂L, hne⟩
    let p : {p : PFlat ℝ (d + 1) 2 × PFlat ℝ (d + 1) 2 // p ∈ L.offDiag} := ⟨(l₁, l₂), hp⟩
    have heq : witness p = x := by
      have hshare : ∃ y : PFlat ℝ (d + 1) 1, y.1 ≤ l₁.1 ∧ y.1 ≤ l₂.1 :=
        ⟨x, hx₁, hx₂⟩
      dsimp [witness]
      rw [dif_pos hshare]
      exact projectivePoint_eq_of_two_lines hne
        (Classical.choose_spec hshare).1
        (Classical.choose_spec hshare).2 hx₁ hx₂
    rw [← heq]
    change witness p ∈ L.offDiag.attach.image witness
    exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ p, rfl⟩
  exact ⟨T, hsub, hTcard⟩

private theorem projective_rich_lines_pair_cover {d : ℕ}
    (X : Finset (PFlat ℝ (d + 1) 1)) (k : ℕ) (hk : 2 ≤ k) :
    ∃ T : Finset (PFlat ℝ (d + 1) 2),
      {l : PFlat ℝ (d + 1) 2 | k ≤ (X.filter (fun x => x.1 ≤ l.1)).card} ⊆
        (T : Set (PFlat ℝ (d + 1) 2)) ∧
        T.card ≤ X.card ^ 2 := by
  classical
  let pairLine (p : {p : PFlat ℝ (d + 1) 1 × PFlat ℝ (d + 1) 1 // p ∈ X.offDiag}) :=
    projectiveLineThroughPoints p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2
  let T := X.offDiag.attach.image pairLine
  have hTcard : T.card ≤ X.card ^ 2 := by
    dsimp [T]
    calc
      _ ≤ X.offDiag.attach.card := Finset.card_image_le
      _ = X.offDiag.card := Finset.card_attach
      _ ≤ X.card ^ 2 := by
        rw [Finset.offDiag_card]
        calc
          X.card * X.card - X.card ≤ X.card * X.card := Nat.sub_le _ _
          _ = X.card ^ 2 := by simp [pow_two]
  have hsub : {l : PFlat ℝ (d + 1) 2 | k ≤ (X.filter (fun x => x.1 ≤ l.1)).card} ⊆
      (T : Set (PFlat ℝ (d + 1) 2)) := by
    intro l hl
    have hcard : 2 ≤ (X.filter (fun x => x.1 ≤ l.1)).card := hk.trans hl
    obtain ⟨x, y, hx, hy, hne⟩ :=
      Finset.one_lt_card_iff.mp (show 1 < (X.filter (fun x => x.1 ≤ l.1)).card by omega)
    rcases Finset.mem_filter.mp hx with ⟨hxX, hxl⟩
    rcases Finset.mem_filter.mp hy with ⟨hyX, hyl⟩
    have hp : (x, y) ∈ X.offDiag := by
      rw [Finset.mem_offDiag]
      exact ⟨hxX, hyX, hne⟩
    let p : {p : PFlat ℝ (d + 1) 1 × PFlat ℝ (d + 1) 1 // p ∈ X.offDiag} := ⟨(x, y), hp⟩
    have hline : pairLine p = l :=
      projectiveLineThroughPoints_eq_of_contains x y hne l hxl hyl
    change l ∈ X.offDiag.attach.image pairLine
    rw [← hline]
    exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ p, rfl⟩
  exact ⟨T, hsub, hTcard⟩

private theorem finsupp_exp_sum_le_one {m : Fin 3 →₀ ℕ}
    (hm : m.sum (fun _ e => e) ≤ 1) :
    m = 0 ∨ ∃ i : Fin 3, m = Finsupp.single i 1 := by
  classical
  have hsum : (∑ i : Fin 3, m i) ≤ 1 := by simpa [Finsupp.sum_fintype] using hm
  have hsupp : m.support.card ≤ 1 := by
    calc
      m.support.card = ∑ i ∈ m.support, 1 := by simp
      _ ≤ ∑ i ∈ m.support, m i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      _ = m.sum (fun _ e => e) := by simp [Finsupp.sum]
      _ ≤ 1 := hm
  by_cases hne : m.support.Nonempty
  · have hcard : m.support.card = 1 := by
      have hpos := Finset.card_pos.mpr hne
      omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have hmi : m i = 1 := by
      have hiMem : i ∈ m.support := by rw [hi]; simp
      have hmi0 : 0 < m i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hiMem)
      have hmiLe : m i ≤ m.sum (fun _ e => e) := by
        simpa using Finsupp.single_le_sum (f := m) (g := fun _ e => e)
          (fun _ _ => Nat.zero_le _) i
      omega
    right
    refine ⟨i, ?_⟩
    ext j
    by_cases hji : j = i
    · subst j
      simp [hmi]
    · have hjnot : j ∉ m.support := by rw [hi]; simp [hji]
      have hmj : m j = 0 := by
        by_contra hmj
        exact hjnot (Finsupp.mem_support_iff.mpr hmj)
      simp [hmj, hji]
  · left
    exact Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hne)

private theorem totalDegree_one_as_affine (p : Poly 3) (hp : p.totalDegree = 1) :
    p = MvPolynomial.C (p.coeff 0) +
      ∑ i : Fin 3, MvPolynomial.C (p.coeff (Finsupp.single i 1)) * MvPolynomial.X i := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases hm0 : m = 0
  · subst m
    simp
  · by_cases hms : ∃ i : Fin 3, m = Finsupp.single i 1
    · rcases hms with ⟨i, rfl⟩
      have hne0 : Finsupp.single i 1 ≠ (0 : Fin 3 →₀ ℕ) := by simp
      simp [Ne.symm hne0, MvPolynomial.coeff_X, MvPolynomial.coeff_C_mul,
        Finsupp.single_eq_single_iff]
    · have hdeg : 1 < ∑ i ∈ m.support, m i := by
        by_contra h
        have hmle : m.sum (fun _ e => e) ≤ 1 := by
          have h' : ∑ i ∈ m.support, m i ≤ 1 := by omega
          simpa [Finsupp.sum] using h'
        rcases finsupp_exp_sum_le_one hmle with hmzero | ⟨i, hi⟩
        · exact hm0 hmzero
        · exact hms ⟨i, hi⟩
      have hcoeff : p.coeff m = 0 := by
        apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        rw [hp]
        exact hdeg
      have hneSingle (i : Fin 3) : m ≠ Finsupp.single i 1 := by
        intro heq
        exact hms ⟨i, heq⟩
      have hneSingle' (i : Fin 3) : Finsupp.single i 1 ≠ m := (hneSingle i).symm
      have hzero0 : (0 : Fin 3 →₀ ℕ) ≠ m := fun h => hm0 h.symm
      simp [hzero0, hcoeff, hneSingle', MvPolynomial.coeff_X, MvPolynomial.coeff_C_mul,
        Finsupp.single_eq_single_iff]

private noncomputable def affineLinearPart (p : Poly 3) : E 3 →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin 3, p.coeff (Finsupp.single i 1) * x i
  map_add' := by
    intro x y
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro a x
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private theorem eval_totalDegree_one (p : Poly 3) (hp : p.totalDegree = 1) (x : E 3) :
    evalR p x = p.coeff 0 + affineLinearPart p x := by
  unfold evalR
  conv_lhs => rw [totalDegree_one_as_affine p hp]
  simp [affineLinearPart, MvPolynomial.eval_add, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, mul_comm]

private theorem affineLinearPart_ne_zero (p : Poly 3) (hp : p.totalDegree = 1) :
    affineLinearPart p ≠ 0 := by
  intro hzero
  have hcoeff (i : Fin 3) : p.coeff (Finsupp.single i 1) = 0 := by
    let e : E 3 := WithLp.toLp 2 (Pi.single i (1 : ℝ))
    have heval : affineLinearPart p e = p.coeff (Finsupp.single i 1) := by
      simp [affineLinearPart, e]
    have h := congrArg (fun F : E 3 →ₗ[ℝ] ℝ => F e) hzero
    simpa [heval] using h
  have hconst : p = MvPolynomial.C (p.coeff 0) := by
    rw [totalDegree_one_as_affine p hp]
    simp [hcoeff]
  rw [hconst] at hp
  simp at hp

private theorem exists_plane_for_linear_polynomial (p : Poly 3) (hp : p.totalDegree = 1) :
    ∃ H : Plane 3, ∀ l : Line 3, onPolynomial p l → l.1 ≤ H.1 := by
  classical
  have hA : affineLinearPart p ≠ 0 := affineLinearPart_ne_zero p hp
  have hcoeff : ∃ i : Fin 3, p.coeff (Finsupp.single i 1) ≠ 0 := by
    by_contra h
    have hcoeffZero (i : Fin 3) : p.coeff (Finsupp.single i 1) = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    apply hA
    ext x
    simp [affineLinearPart, hcoeffZero]
  obtain ⟨i, hi⟩ := hcoeff
  let A := affineLinearPart p
  let e : E 3 := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  have hAe : A e = p.coeff (Finsupp.single i 1) := by
    simp [A, affineLinearPart, e]
  have hsurj : Function.Surjective A := by
    intro y
    refine ⟨(y / p.coeff (Finsupp.single i 1)) • e, ?_⟩
    rw [map_smul, hAe, smul_eq_mul]
    field_simp [hi]
  let x₀ : E 3 := Classical.choose (hsurj (-p.coeff 0))
  have hx₀ : A x₀ = -p.coeff 0 := Classical.choose_spec (hsurj (-p.coeff 0))
  let H : AffineSubspace ℝ (E 3) := AffineSubspace.mk' x₀ A.ker
  have hdim : Module.finrank ℝ A.ker = 2 := by
    have h := A.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    have hE : Module.finrank ℝ (E 3) = 3 := by simp [E]
    have htop : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by simp
    rw [htop, hE] at h
    omega
  let Hplane : Plane 3 := ⟨H, ⟨x₀, AffineSubspace.self_mem_mk' x₀ A.ker⟩, by
    rw [AffineSubspace.direction_mk']
    exact hdim⟩
  refine ⟨Hplane, ?_⟩
  intro l hl
  intro x hx
  change x ∈ AffineSubspace.mk' x₀ A.ker
  rw [AffineSubspace.mem_mk']
  have hevalZero : p.coeff 0 + A x = 0 := by
    rw [← eval_totalDegree_one p hp x]
    exact hl x hx
  have hAx : A x = A x₀ := by linarith [hx₀]
  have hdiff : A (x -ᵥ x₀) = A x - A x₀ := by simp [vsub_eq_sub]
  change A (x -ᵥ x₀) = 0
  rw [hdiff, hAx]
  simp

private theorem linearPolynomial_irreducible (p : Poly 3) (hp : p.totalDegree = 1) :
    Irreducible p := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, MvPolynomial.totalDegree_zero] at hp
    omega
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
    omega
  · intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    by_cases hb : IsUnit b
    · exact Or.inr hb
    have ha0 : a ≠ 0 := by
      intro hz
      subst a
      simp at hab
      exact hp0 hab
    have hb0 : b ≠ 0 := by
      intro hz
      subst b
      simp at hab
      exact hp0 hab
    have hpos (q : Poly 3) (hq0 : q ≠ 0) (hqunit : ¬ IsUnit q) :
        1 ≤ q.totalDegree := by
      by_contra h
      have hdeg0 : q.totalDegree = 0 := by omega
      have hcoeff0 : q.coeff 0 ≠ 0 := by
        intro hc
        apply hq0
        rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0, hc]
        simp
      have hqUnit : IsUnit q := by
        apply (MvPolynomial.isUnit_iff_eq_C_of_isReduced).2
        exact ⟨q.coeff 0, isUnit_iff_ne_zero.mpr hcoeff0,
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0⟩
      exact hqunit hqUnit
    have hadeg := hpos a ha0 ha
    have hbdeg := hpos b hb0 hb
    have hdegprod : a.totalDegree + b.totalDegree = 1 := by
      calc
        a.totalDegree + b.totalDegree = (a * b).totalDegree :=
          (MvPolynomial.totalDegree_mul_of_isDomain ha0 hb0).symm
        _ = p.totalDegree := congrArg MvPolynomial.totalDegree hab.symm
        _ = 1 := hp
    omega

private theorem multiset_card_le_sum_nat {α : Type*} (s : Multiset α) (f : α → ℕ)
    (hf : ∀ a ∈ s, 1 ≤ f a) : s.card ≤ (s.map f).sum := by
  classical
  revert hf
  induction s using Multiset.induction_on with
  | empty => intro; simp
  | @cons a s ih =>
    intro hf
    have htail : ∀ b ∈ s, 1 ≤ f b := by
      intro b hb
      exact hf b (by simp [hb])
    have hhead := hf a (by simp)
    have hrec := ih htail
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    omega

private theorem multiset_totalDegree_prod_eq_sum (s : Multiset (Poly 3))
    (hs : ∀ p ∈ s, p ≠ 0) :
    s.prod.totalDegree = (s.map fun p => p.totalDegree).sum := by
  classical
  revert hs
  induction s using Multiset.induction_on with
  | empty => intro; simp
  | @cons p s ih =>
    intro hs
    have hp : p ≠ 0 := hs p (by simp)
    have hs' : ∀ q ∈ s, q ≠ 0 := by
      intro q hq
      exact hs q (by simp [hq])
    have hsprod : s.prod ≠ 0 := Multiset.prod_ne_zero (by
      intro hzero
      exact hs' 0 hzero rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      MvPolynomial.totalDegree_mul_of_isDomain hp hsprod, ih hs']

private noncomputable instance polyThreeStrongNormalization : StrongNormalizationMonoid (Poly 3) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

private theorem normalizedFactors_card_le_totalDegree (f : Poly 3) (hf : f ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors f).toFinset.card ≤ f.totalDegree := by
  classical
  let nf := UniqueFactorizationMonoid.normalizedFactors f
  have hfactorPos (q : Poly 3) (hq : q ∈ nf) : 1 ≤ q.totalDegree := by
    have hqIrred : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hq0 : q ≠ 0 := by
      intro hz
      exact (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f)
        (by simpa [nf, hz] using hq)
    by_contra hlt
    have hdeg0 : q.totalDegree = 0 := by omega
    have hcoeff0 : q.coeff 0 ≠ 0 := by
      intro hc
      apply hq0
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0, hc]
      simp
    have hqUnit : IsUnit q := by
      apply MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
      exact ⟨q.coeff 0, isUnit_iff_ne_zero.mpr hcoeff0,
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0⟩
    exact hqIrred.not_isUnit hqUnit
  have hcard : nf.card ≤ (nf.map fun q => q.totalDegree).sum :=
    multiset_card_le_sum_nat nf (fun q => q.totalDegree) hfactorPos
  have hprodNe : nf.prod ≠ 0 := Multiset.prod_ne_zero (by
    intro hzero
    exact (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f) (by simpa [nf, hzero]))
  have hprodDeg := multiset_totalDegree_prod_eq_sum nf (by
    intro q hq hq0
    exact (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f)
      (by simpa [nf, hq0] using hq))
  have hAssoc : Associated nf.prod f := by
    simpa [nf] using UniqueFactorizationMonoid.prod_normalizedFactors hf
  have hdegEq : nf.prod.totalDegree = f.totalDegree := by
    apply le_antisymm
    · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hAssoc.dvd hf
    · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hAssoc.symm.dvd hprodNe
  calc
    nf.toFinset.card ≤ nf.card := Multiset.toFinset_card_le _
    _ ≤ (nf.map fun q => q.totalDegree).sum := hcard
    _ = nf.prod.totalDegree := hprodDeg.symm
    _ = f.totalDegree := hdegEq

private theorem partition_cells_cover_sample (S : Finset (E 3)) (f : Poly 3)
    (cells : Finset (Set (E 3)))
    (hdisj : ∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R')
    (hunion : (⋃ R ∈ cells, R) = (zeroSet f)ᶜ) :
    (S.filter (fun x => x ∉ zeroSet f)).card ≤
      ∑ R ∈ cells, (pointsIn S R).card := by
  classical
  let X₀ := S.filter (fun x => x ∉ zeroSet f)
  have hpairs : (cells : Set (Set (E 3))).PairwiseDisjoint (fun R => pointsIn S R) := by
    intro R hR R' hR' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hxR : x ∈ R := (Finset.mem_filter.mp hx).2
    have hxR' : x ∈ R' := (Finset.mem_filter.mp hx').2
    exact (Set.disjoint_left.mp (hdisj R hR R' hR' hne) hxR) hxR'
  have hcover : (X₀ : Set (E 3)) ⊆ (cells.biUnion (pointsIn S) : Set (E 3)) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxnot⟩
    have hxComp : x ∈ (zeroSet f)ᶜ := by simpa using hxnot
    have hxUnion : x ∈ ⋃ R ∈ cells, R := by rw [hunion]; exact hxComp
    rcases Set.mem_iUnion.mp hxUnion with ⟨R, hxUnion⟩
    rcases Set.mem_iUnion.mp hxUnion with ⟨hR, hxR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨R, hR, ?_⟩
    exact Finset.mem_filter.mpr ⟨hxS, hxR⟩
  calc
    X₀.card ≤ (cells.biUnion (pointsIn S)).card := Finset.card_le_card hcover
    _ = ∑ R ∈ cells, (pointsIn S R).card := Finset.card_biUnion hpairs

private theorem exists_le_real_average_plus_one {α : Type*} (H : Finset α)
    (g : α → ℕ) (hH : H.Nonempty) (T : ℝ)
    (hT : (∑ a ∈ H, (g a : ℝ)) ≤ T) :
    ∃ a ∈ H, (g a : ℝ) ≤ T / H.card + 1 := by
  by_contra h
  have hstrict : ∀ a ∈ H, T / H.card + 1 < (g a : ℝ) := by
    intro a ha
    exact lt_of_not_ge (by intro hge; exact h ⟨a, ha, hge⟩)
  have hsum := Finset.sum_lt_sum_of_nonempty hH hstrict
  have hconst : (∑ _a ∈ H, (T / H.card + 1)) = T + H.card := by
    calc
      _ = (H.card : ℝ) * (T / H.card + 1) := by simp <;> ring
      _ = T + H.card := by
        have hpos : (H.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hH.card_pos)
        field_simp [hpos]
        <;> ring
  rw [hconst] at hsum
  have hcardpos : (0 : ℝ) < H.card := Nat.cast_pos.mpr hH.card_pos
  linarith

private theorem finset_rich_points_bound {d : ℕ} (X : Finset (E d))
    (L : Finset (Line d)) (k : ℕ) (hk : 2 ≤ k)
    (hinc : ∀ x ∈ X, k ≤ lineMultiplicity L x) :
    ∃ C : ℝ, 0 < C ∧
      (X.card : ℝ) ≤ C * ((L.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (L.card : ℝ) / k) := by
  obtain ⟨C, hCpos, hC⟩ := ci_st_rich
  have hsetBound := (hC d X L k hk).1
  have hsub : (X : Set (E d)) ⊆ richPoints L k := by
    intro x hx
    simpa [richPoints] using hinc x hx
  have hcard := Set.ncard_le_ncard hsub hsetBound.1
  rw [Set.ncard_coe_finset] at hcard
  refine ⟨C, hCpos, ?_⟩
  have hcardReal : (X.card : ℝ) ≤ (richPoints L k).ncard := by exact_mod_cast hcard
  exact hcardReal.trans hsetBound.2

private theorem polynomial_zero_residual_bound (g : Poly 3) (S : Finset (E 3))
    (L : Finset (Line 3)) (k : ℕ) (hk : 3 ≤ k)
    (hmult : ∀ x ∈ S, k ≤ lineMultiplicity L x) :
    let Lz := L.filter (fun l => onPolynomial g l)
    let Lout := L.filter (fun l => ¬ onPolynomial g l)
    ((S.filter (fun x => x ∈ zeroSet g ∧ lineMultiplicity Lz x < 3)).card * (k - 2)) ≤
      L.card * g.totalDegree := by
  classical
  let Lz := L.filter (fun l => onPolynomial g l)
  let Lout := L.filter (fun l => ¬ onPolynomial g l)
  let Sbad := S.filter (fun x => x ∈ zeroSet g ∧ lineMultiplicity Lz x < 3)
  have hsplit (x : E 3) : lineMultiplicity L x =
      lineMultiplicity Lz x + lineMultiplicity Lout x := by
    unfold lineMultiplicity
    have h := (L.filter (fun l => x ∈ l.1)).card_filter_add_card_filter_not
      (fun l => onPolynomial g l)
    simpa [Lz, Lout, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using h.symm
  have hbadMult (x : E 3) (hx : x ∈ Sbad) :
      k - 2 ≤ lineMultiplicity Lout x := by
    rcases Finset.mem_filter.mp hx with ⟨hxS, ⟨hxzero, hLzlt⟩⟩
    have htotal := hmult x hxS
    rw [hsplit] at htotal
    omega
  have hTbound (l : Line 3) (hl : l ∈ Lout) :
      (S.filter (fun x => x ∈ l.1 ∧ evalR g x = 0)).card ≤ g.totalDegree := by
    let T := S.filter (fun x => x ∈ l.1 ∧ evalR g x = 0)
    by_contra h
    have hdegree : g.totalDegree < T.card := Nat.lt_of_not_ge h
    have hTmem : ∀ x ∈ T, x ∈ l.1 ∧ evalR g x = 0 := by
      intro x hx
      simpa [T] using (Finset.mem_filter.mp hx).2
    have hpoly := polynomial_line_zeros 3 g l T hTmem hdegree
    exact (Finset.mem_filter.mp hl).2 hpoly
  have hcountLower : Sbad.card * (k - 2) ≤ ∑ x ∈ Sbad, lineMultiplicity Lout x := by
    calc
      Sbad.card * (k - 2) = ∑ x ∈ Sbad, (k - 2) := by simp
      _ ≤ ∑ x ∈ Sbad, lineMultiplicity Lout x := by
        apply Finset.sum_le_sum
        intro x hx
        exact hbadMult x hx
  have hcountEq : (∑ x ∈ Sbad, lineMultiplicity Lout x) =
      ∑ l ∈ Lout, (Sbad.filter (fun x => x ∈ l.1)).card := by
    unfold lineMultiplicity
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := Lout) (t := Sbad) (r := fun l x => x ∈ l.1)).symm
  have hcountUpper :
      (∑ l ∈ Lout, (Sbad.filter (fun x => x ∈ l.1)).card) ≤
        L.card * g.totalDegree := by
    calc
      _ ≤ ∑ l ∈ Lout, g.totalDegree := by
        apply Finset.sum_le_sum
        intro l hl
        have hsub : Sbad.filter (fun x => x ∈ l.1) ⊆
            S.filter (fun x => x ∈ l.1 ∧ evalR g x = 0) := by
          intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hxSbad, hxl⟩
          rcases Finset.mem_filter.mp hxSbad with ⟨hxS, ⟨hxzero, _⟩⟩
          exact Finset.mem_filter.mpr ⟨hxS, hxl, hxzero⟩
        exact (Finset.card_le_card hsub).trans (hTbound l hl)
      _ = Lout.card * g.totalDegree := by simp
      _ ≤ L.card * g.totalDegree := by
        exact Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
  dsimp [Lz, Lout, Sbad]
  calc
    _ ≤ ∑ x ∈ Sbad, lineMultiplicity Lout x := hcountLower
    _ = ∑ l ∈ Lout, (Sbad.filter (fun x => x ∈ l.1)).card := hcountEq
    _ ≤ L.card * g.totalDegree := hcountUpper

private theorem ci_st_rich_finite_card : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Finset (E d)) (L : Finset (Line d)) (k : ℕ), 2 ≤ k →
      (∀ x ∈ X, k ≤ lineMultiplicity L x) →
      (X.card : ℝ) ≤ C * ((L.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (L.card : ℝ) / k) := by
  obtain ⟨C, hCpos, hC⟩ := ci_st_rich
  refine ⟨C, hCpos, ?_⟩
  intro d X L k hk hinc
  have hsetBound := (hC d X L k hk).1
  have hsub : (X : Set (E d)) ⊆ richPoints L k := by
    intro x hx
    simpa [richPoints] using hinc x hx
  have hcard := Set.ncard_le_ncard hsub hsetBound.1
  rw [Set.ncard_coe_finset] at hcard
  have hcardReal : (X.card : ℝ) ≤ (richPoints L k).ncard := by exact_mod_cast hcard
  exact hcardReal.trans hsetBound.2

private theorem ci_partition_3d_interface : ∃ P : ℝ, 0 < P ∧ 1 ≤ P ∧
    ∀ (S : Finset (E 3)) (r : ℕ), 1 ≤ r →
      ∃ (f : Poly 3) (cells : Finset (Set (E 3))),
        f ≠ 0 ∧ (f.totalDegree : ℝ) ≤ P * r ∧
        (cells.card : ℝ) ≤ P * (r : ℝ) ^ 3 ∧
        (∀ R ∈ cells, ((pointsIn S R).card : ℝ) ≤ P * S.card / (r : ℝ) ^ 3) ∧
        (∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R') ∧
        (⋃ R ∈ cells, R) = (zeroSet f)ᶜ ∧
        (∀ l : Line 3, ¬ onPolynomial f l →
          (cells.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card ≤
            f.totalDegree + 1) := by
  obtain ⟨C, hCpos, hC⟩ := ci_partition
  let P := C + 1
  have hPpos : 0 < P := by dsimp [P]; linarith
  have hPge : 1 ≤ P := by dsimp [P]; linarith
  refine ⟨P, hPpos, hPge, ?_⟩
  intro S r hr
  obtain ⟨f, cells, hf, hdeg, hcard, hocc, hdisj, hunion, hcross⟩ := hC S r hr
  refine ⟨f, cells, hf, ?_, ?_, ?_, hdisj, hunion, hcross⟩
  · have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    dsimp [P]
    nlinarith [hdeg]
  · have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    dsimp [P]
    nlinarith [hcard]
  · intro R hR
    have h := hocc R hR
    have hratio : 0 ≤ (S.card : ℝ) / (r : ℝ) ^ 3 := by positivity
    have hCstep : C ≤ C + 1 := le_add_of_nonneg_right (by norm_num)
    dsimp [P]
    calc
      ((pointsIn S R).card : ℝ) ≤ C * S.card / (r : ℝ) ^ 3 := h.2
      _ = C * ((S.card : ℝ) / (r : ℝ) ^ 3) := by ring
      _ ≤ (C + 1) * ((S.card : ℝ) / (r : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right hCstep hratio
      _ = (C + 1) * S.card / (r : ℝ) ^ 3 := by ring

set_option maxHeartbeats 500000 in
private theorem no_large_partition_solution {L s k r theta K A : ℝ}
    (hL : 0 < L) (hs : 0 < s) (hk : 0 < k) (hk1 : 1 ≤ k) (hr : 0 < r)
    (htheta : 0 < theta) (hA : 0 < A) (hAone : 1 ≤ A)
    (hK : 0 ≤ K)
    (hpow : (L ^ ((3 : ℝ) / 2) / k ^ 2) ^ 2 = L ^ 3 / k ^ 4)
    (hQlow : theta * L ^ 2 / (s * k ^ 3) ≤ r)
    (hQhigh : r ≤ 2 * theta * L ^ 2 / (s * k ^ 3))
    (hLarge : A * (L ^ ((3 : ℝ) / 2) / k ^ 2 + L / k) < s)
    (hKtheta : K / theta ≤ 1 / 4)
    (hKA : 2 * K * theta / A ≤ 1 / 4)
    (hKA4 : 8 * K * theta ^ 3 / A ^ 4 ≤ 1 / 4)
    (hcell : s ≤ K * (L ^ 2 / (r * k ^ 3) + L * r / k + r ^ 3 / k)) : False := by
  let u : ℝ := L ^ ((3 : ℝ) / 2) / k ^ 2
  have hu : 0 < u := by dsimp [u]; positivity
  have huSmall : u < s / A := by
    dsimp [u]
    have hmain : A * (L ^ ((3 : ℝ) / 2) / k ^ 2) < s := by
      have hnonneg : 0 ≤ L / k := div_nonneg hL.le hk.le
      have hlinear : 0 ≤ A * (L / k) := mul_nonneg hA.le hnonneg
      linarith [hLarge]
    exact (lt_div_iff₀ hA).2 (by simpa [mul_comm] using hmain)
  have hqcross : theta * L ^ 2 ≤ r * s * k ^ 3 := by
    have h := (div_le_iff₀ (mul_pos hs (pow_pos hk 3))).mp hQlow
    nlinarith [h]
  have hterm1 : L ^ 2 / (r * k ^ 3) ≤ s / theta := by
    apply (div_le_div_iff₀ (mul_pos hr (pow_pos hk 3)) htheta).2
    nlinarith [hqcross]
  have hterm2a : L * r / k ≤ 2 * theta * L ^ 3 / (s * k ^ 4) := by
    apply (div_le_iff₀ hk).2
    calc
      L * r ≤ L * (2 * theta * L ^ 2 / (s * k ^ 3)) :=
        mul_le_mul_of_nonneg_left hQhigh hL.le
      _ = (2 * theta * L ^ 3 / (s * k ^ 4)) * k := by
        field_simp [ne_of_gt hs, ne_of_gt hk]
        <;> ring
  have hu2 : u ^ 2 ≤ s ^ 2 / A ^ 2 :=
    calc
      u ^ 2 ≤ (s / A) ^ 2 := pow_le_pow_left₀ hu.le huSmall.le 2
      _ = s ^ 2 / A ^ 2 := by ring
  have hterm2b : L ^ 3 / (s * k ^ 4) ≤ s / A ^ 2 := by
    have hrewrite : L ^ 3 / (s * k ^ 4) = u ^ 2 / s := by
      calc
        L ^ 3 / (s * k ^ 4) = (L ^ 3 / k ^ 4) / s := by
          field_simp [ne_of_gt hs, ne_of_gt hk]
          <;> ring
        _ = u ^ 2 / s := by rw [← hpow]
    rw [hrewrite]
    calc
      u ^ 2 / s ≤ (s ^ 2 / A ^ 2) / s := div_le_div_of_nonneg_right hu2 hs.le
      _ = s / A ^ 2 := by field_simp [ne_of_gt hs] <;> ring
  have hterm2 : L * r / k ≤ 2 * theta * s / A ^ 2 := by
    calc
      L * r / k ≤ 2 * theta * L ^ 3 / (s * k ^ 4) := hterm2a
      _ = 2 * theta * (L ^ 3 / (s * k ^ 4)) := by ring
      _ ≤ 2 * theta * (s / A ^ 2) :=
        mul_le_mul_of_nonneg_left hterm2b (by positivity : 0 ≤ 2 * theta)
      _ = 2 * theta * s / A ^ 2 := by ring
  have hterm3a : r ^ 3 / k ≤ (2 * theta * L ^ 2 / (s * k ^ 3)) ^ 3 / k := by
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr.le hQhigh 3) hk.le
  have hu4 : u ^ 4 ≤ s ^ 4 / A ^ 4 := by
    calc
      u ^ 4 ≤ (s / A) ^ 4 := pow_le_pow_left₀ hu.le huSmall.le 4
      _ = s ^ 4 / A ^ 4 := by ring
  have hterm3b : (2 * theta * L ^ 2 / (s * k ^ 3)) ^ 3 / k =
      8 * theta ^ 3 * u ^ 4 / (s ^ 3 * k ^ 2) := by
    have hpow4 : u ^ 4 = L ^ 6 / k ^ 8 := by
      calc
        u ^ 4 = (u ^ 2) ^ 2 := by ring
        _ = (L ^ 3 / k ^ 4) ^ 2 := by rw [hpow]
        _ = L ^ 6 / k ^ 8 := by rw [div_pow]; ring
    rw [div_pow, hpow4]
    field_simp [ne_of_gt hs, ne_of_gt hk]
    <;> ring
  have hterm3c : u ^ 4 / (s ^ 3 * k ^ 2) ≤ s / A ^ 4 := by
    have hkSq : 1 ≤ k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
    have hden : s ^ 3 ≤ s ^ 3 * k ^ 2 := by nlinarith [pow_pos hs 3, hkSq]
    calc
      u ^ 4 / (s ^ 3 * k ^ 2) ≤ u ^ 4 / s ^ 3 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_left hden (by positivity)
      _ ≤ (s ^ 4 / A ^ 4) / s ^ 3 := div_le_div_of_nonneg_right hu4 (by positivity)
      _ = s / A ^ 4 := by field_simp [ne_of_gt hs] <;> ring
  have hterm3 : r ^ 3 / k ≤ 8 * theta ^ 3 * s / A ^ 4 := by
    calc
      r ^ 3 / k ≤ (2 * theta * L ^ 2 / (s * k ^ 3)) ^ 3 / k := hterm3a
      _ = 8 * theta ^ 3 * u ^ 4 / (s ^ 3 * k ^ 2) := hterm3b
      _ = (8 * theta ^ 3) * (u ^ 4 / (s ^ 3 * k ^ 2)) := by ring
      _ ≤ (8 * theta ^ 3) * (s / A ^ 4) :=
        mul_le_mul_of_nonneg_left hterm3c (by positivity : 0 ≤ 8 * theta ^ 3)
      _ = 8 * theta ^ 3 * s / A ^ 4 := by ring
  have hsum : s ≤ K * (s / theta + 2 * theta * s / A ^ 2 + 8 * theta ^ 3 * s / A ^ 4) := by
    calc
      s ≤ K * (L ^ 2 / (r * k ^ 3) + L * r / k + r ^ 3 / k) := hcell
      _ ≤ K * (s / theta + 2 * theta * s / A ^ 2 + 8 * theta ^ 3 * s / A ^ 4) := by
        gcongr
  have hfrac1 : K * (s / theta) ≤ s / 4 := by
    calc
      K * (s / theta) = (K / theta) * s := by ring
      _ ≤ (1 / 4) * s := mul_le_mul_of_nonneg_right hKtheta hs.le
      _ = s / 4 := by ring
  have hfrac2 : K * (2 * theta * s / A ^ 2) ≤ s / 4 := by
    have hInv : 1 / A ^ 2 ≤ 1 / A := by
      apply (div_le_div_iff₀ (by positivity) hA).2
      have hprod := mul_nonneg (le_of_lt hA) (sub_nonneg.mpr hAone)
      nlinarith [hprod]
    have hInvScaled : 2 * K * theta / A ^ 2 ≤ 2 * K * theta / A := by
      calc
        2 * K * theta / A ^ 2 = (2 * K * theta) * (1 / A ^ 2) := by ring
        _ ≤ (2 * K * theta) * (1 / A) :=
          mul_le_mul_of_nonneg_left hInv (by positivity : 0 ≤ 2 * K * theta)
        _ = 2 * K * theta / A := by ring
    calc
      K * (2 * theta * s / A ^ 2) = (2 * K * theta / A ^ 2) * s := by ring
      _ ≤ (2 * K * theta / A) * s :=
        mul_le_mul_of_nonneg_right hInvScaled hs.le
      _ ≤ (1 / 4) * s := mul_le_mul_of_nonneg_right hKA hs.le
      _ = s / 4 := by ring
  have hfrac3 : K * (8 * theta ^ 3 * s / A ^ 4) ≤ s / 4 := by
    calc
      K * (8 * theta ^ 3 * s / A ^ 4) = (8 * K * theta ^ 3 / A ^ 4) * s := by ring
      _ ≤ (1 / 4) * s := mul_le_mul_of_nonneg_right hKA4 hs.le
      _ = s / 4 := by ring
  have hcontra : s ≤ 3 * s / 4 := by
    calc
      s ≤ K * (s / theta) + K * (2 * theta * s / A ^ 2) +
          K * (8 * theta ^ 3 * s / A ^ 4) := by
        calc
          s ≤ K * (s / theta + 2 * theta * s / A ^ 2 + 8 * theta ^ 3 * s / A ^ 4) := hsum
          _ = _ := by ring
      _ ≤ s / 4 + s / 4 + s / 4 := add_le_add (add_le_add hfrac1 hfrac2) hfrac3
      _ = 3 * s / 4 := by ring
  linarith

/-- Projective rich-line/point form, used by the second Beck application. -/
theorem ci_st_rich_projective : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Finset (PFlat ℝ (d + 1) 1))
      (L : Finset (PFlat ℝ (d + 1) 2)) (k : ℕ), 2 ≤ k →
      FiniteCardBound {x : PFlat ℝ (d + 1) 1 | k ≤ (L.filter (fun l => x.1 ≤ l.1)).card}
        (C * ((L.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (L.card : ℝ) / k)) ∧
      FiniteCardBound {l : PFlat ℝ (d + 1) 2 | k ≤ (X.filter (fun x => x.1 ≤ l.1)).card}
        (C * ((X.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (X.card : ℝ) / k)) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := ci_st_projective
  refine ⟨72 * C₀ ^ 3 + 4 * C₀ + 1, by positivity, ?_⟩
  intro d X L k hk
  constructor
  · obtain ⟨T, hcover, hTcard⟩ := projective_rich_points_pair_cover L k hk
    let Rset : Set (PFlat ℝ (d + 1) 1) :=
      {x | k ≤ (L.filter (fun l => x.1 ≤ l.1)).card}
    have hR : Rset.Finite := (Finset.finite_toSet T).subset hcover
    let R := hR.toFinset
    have hRcard : Rset.ncard = R.card := by
      simpa [R] using Set.ncard_eq_toFinset_card Rset hR
    have hRsub : R ⊆ T := by
      intro x hx
      exact hcover (hR.mem_toFinset.mp hx)
    have hRpair : R.card ≤ L.card ^ 2 := (Finset.card_le_card hRsub).trans hTcard
    have hLowerNat : R.card * k ≤ projectiveIncidences d R L := by
      change R.card * k ≤ ∑ x ∈ R, (L.filter (fun l => x.1 ≤ l.1)).card
      calc
        R.card * k = ∑ x ∈ R, k := by simp
        _ ≤ ∑ x ∈ R, (L.filter (fun l => x.1 ≤ l.1)).card := by
          apply Finset.sum_le_sum
          intro x hx
          have hxR := hR.mem_toFinset.mp hx
          simpa [Rset] using hxR
    have hLower : (R.card : ℝ) * (k : ℝ) ≤
        (projectiveIncidences d R L : ℝ) := by exact_mod_cast hLowerNat
    have hpair : (R.card : ℝ) ≤ (L.card : ℝ) ^ 2 := by exact_mod_cast hRpair
    have hIncRaw := hLower.trans (hC₀ d R L)
    have hInc : (k : ℝ) * (R.card : ℝ) ≤ C₀ *
        ((R.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          R.card + L.card) := by
      simpa [mul_comm] using hIncRaw
    have hnum := rich_real_bound (s := (R.card : ℝ)) (n := (L.card : ℝ))
      (k := (k : ℝ)) (C := C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hk) hC₀pos hpair hInc
    refine ⟨hR, ?_⟩
    rw [hRcard]
    exact hnum
  · obtain ⟨T, hcover, hTcard⟩ := projective_rich_lines_pair_cover X k hk
    let Rset : Set (PFlat ℝ (d + 1) 2) :=
      {l | k ≤ (X.filter (fun x => x.1 ≤ l.1)).card}
    have hR : Rset.Finite := (Finset.finite_toSet T).subset hcover
    let R := hR.toFinset
    have hRcard : Rset.ncard = R.card := by
      simpa [R] using Set.ncard_eq_toFinset_card Rset hR
    have hRsub : R ⊆ T := by
      intro l hl
      exact hcover (hR.mem_toFinset.mp hl)
    have hRpair : R.card ≤ X.card ^ 2 := (Finset.card_le_card hRsub).trans hTcard
    have hcount : (∑ l ∈ R, (X.filter (fun x => x.1 ≤ l.1)).card) =
        projectiveIncidences d X R := by
      unfold projectiveIncidences
      simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := R) (t := X) (r := fun l x => x.1 ≤ l.1))
    have hLowerNat : R.card * k ≤ projectiveIncidences d X R := by
      rw [← hcount]
      calc
        R.card * k = ∑ l ∈ R, k := by simp
        _ ≤ ∑ l ∈ R, (X.filter (fun x => x.1 ≤ l.1)).card := by
          apply Finset.sum_le_sum
          intro l hl
          have hlR := hR.mem_toFinset.mp hl
          simpa [Rset] using hlR
    have hLower : (R.card : ℝ) * (k : ℝ) ≤
        (projectiveIncidences d X R : ℝ) := by exact_mod_cast hLowerNat
    have hpair : (R.card : ℝ) ≤ (X.card : ℝ) ^ 2 := by exact_mod_cast hRpair
    have hIncRaw := hLower.trans (hC₀ d X R)
    have hInc : (k : ℝ) * (R.card : ℝ) ≤ C₀ *
        ((R.card : ℝ) ^ ((2 : ℝ) / 3) * (X.card : ℝ) ^ ((2 : ℝ) / 3) +
          R.card + X.card) := by
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hIncRaw
    have hnum := rich_real_bound (s := (R.card : ℝ)) (n := (X.card : ℝ))
      (k := (k : ℝ)) (C := C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hk) hC₀pos hpair hInc
    refine ⟨hR, ?_⟩
    rw [hRcard]
    exact hnum

set_option maxHeartbeats 50000000 in
/-- Uniformity step of ci:rich-lines, CI:225–308. -/
theorem rich_lines_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (L : Finset (Line 3)) (S : Finset (E 3)) (B : ℝ) (k : ℕ),
      L.Nonempty → 0 ≤ B → planeCap L B → 3 ≤ k →
      (∀ x ∈ S, k ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2 * k) →
      (L.card : ℝ) / 100 ≤
        ((L.filter (fun l => (S.card : ℝ) * k / (100 * (L.card : ℝ)) ≤
          (pointsOn S l).card)).card : ℝ) →
      (S.card : ℝ) ≤ C *
        ((L.card : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 +
          (L.card : ℝ) * B / (k : ℝ) ^ 3 + (L.card : ℝ) / k) := by
  classical
  obtain ⟨Cr, hCrpos, hCr⟩ := ci_st_rich
  obtain ⟨P, hPpos, hPge, hPartition⟩ := ci_partition_3d_interface
  let eps : ℝ := 1 / 1000000
  let cH : ℝ := eps / (2 * P)
  let Ccross : ℝ := 2 * P / cH + 1
  let K : ℝ := (2 * P * Cr / eps) * (2 * Ccross ^ 2 + Ccross + 3)
  let theta : ℝ := 4 * K + 4 * Cr + 1
  let ACr : ℝ := 2 * Cr + 1
  let Atheta : ℝ := 2 * theta / 3 + 1
  let AK : ℝ := 8 * K * theta + 1
  let AK4 : ℝ := 32 * K * theta ^ 3 + 1
  let Ares : ℝ := 6 * P * theta / eps + 1
  let A : ℝ := max ACr (max Atheta (max AK (max AK4 Ares)))
  let Cout : ℝ := 800 * P * theta + 1
  let Cfinal : ℝ := A + Cout + 1
  have heps : 0 < eps := by norm_num [eps]
  have hCfinal : 0 < Cfinal := by positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro L S B k hL hB hplane hk hmult huniform
  let s : ℝ := S.card
  let lcnt : ℝ := L.card
  let kr : ℝ := k
  let target : ℝ := lcnt ^ ((3 : ℝ) / 2) / kr ^ 2 + lcnt / kr
  let targetFinal : ℝ := lcnt ^ ((3 : ℝ) / 2) / kr ^ 2 +
    lcnt * B / kr ^ 3 + lcnt / kr
  have hsnonneg : 0 ≤ s := by positivity
  have hLpos : 0 < lcnt := by
    dsimp [lcnt]
    exact_mod_cast hL.card_pos
  have hkpos : 0 < kr := by
    dsimp [kr]
    exact_mod_cast (show 0 < k by omega)
  have htargetNonneg : 0 ≤ target := by positivity
  by_cases hsmall : s ≤ A * target
  · have hCoutnonneg : 0 ≤ Cout := by dsimp [Cout]; positivity
    have hAgeC : A ≤ Cfinal := by dsimp [Cfinal]; linarith
    have htargetLe : target ≤ targetFinal := by
      dsimp [target, targetFinal]
      have hmid : 0 ≤ lcnt * B / kr ^ 3 :=
        div_nonneg (mul_nonneg hLpos.le hB) (by positivity)
      linarith
    have hmulC := mul_le_mul_of_nonneg_right hAgeC htargetNonneg
    have hmulTarget := mul_le_mul_of_nonneg_left htargetLe hCfinal.le
    change (S.card : ℝ) ≤ Cfinal *
      ((L.card : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 +
        (L.card : ℝ) * B / (k : ℝ) ^ 3 + (L.card : ℝ) / k)
    exact hsmall.trans (hmulC.trans hmulTarget)
  · have hLarge : A * target < s := lt_of_not_ge hsmall
    have hSsubset : (S : Set (E 3)) ⊆ richPoints L k := by
      intro x hx
      simpa [richPoints] using (hmult x hx).1
    have hRbound := (hCr 3 S L k (by omega)).1
    have hN := Set.ncard_le_ncard hSsubset hRbound.1
    rw [Set.ncard_coe_finset] at hN
    have hSbound : s ≤ Cr * (lcnt ^ 2 / kr ^ 3 + lcnt / kr) := by
      have hNreal : (S.card : ℝ) ≤ (richPoints L k).ncard := by exact_mod_cast hN
      simpa [s, lcnt, kr] using hNreal.trans hRbound.2
    have hApos : 0 < A := by
      dsimp [A]
      positivity
    have hKpos : 0 < K := by dsimp [K, Ccross, cH]; positivity
    have hACr : 2 * Cr ≤ A := by
      have hfirst : 2 * Cr ≤ ACr := by change 2 * Cr ≤ 2 * Cr + 1; linarith
      exact hfirst.trans (le_max_left _ _)
    have hlinLower : lcnt / kr ≤ target := by
      dsimp [target]
      exact le_add_of_nonneg_left (by positivity)
    have hAline : A * (lcnt / kr) ≤ A * target :=
      mul_le_mul_of_nonneg_left hlinLower hApos.le
    have hlin : lcnt / kr ≤ s / A := by
      apply (le_div_iff₀ hApos).2
      linarith [hAline, hLarge]
    have hCrLine : Cr * (lcnt / kr) ≤ s / 2 := by
      have hratio : Cr / A ≤ 1 / 2 := by
        apply (div_le_iff₀ hApos).2
        nlinarith [hACr]
      calc
        Cr * (lcnt / kr) ≤ Cr * (s / A) := mul_le_mul_of_nonneg_left hlin hCrpos.le
        _ = (Cr / A) * s := by ring
        _ ≤ (1 / 2) * s := mul_le_mul_of_nonneg_right hratio hsnonneg
        _ = s / 2 := by ring
    have hSbound' : s ≤ Cr * lcnt ^ 2 / kr ^ 3 + Cr * (lcnt / kr) := by
      calc
        s ≤ Cr * (lcnt ^ 2 / kr ^ 3 + lcnt / kr) := hSbound
        _ = Cr * lcnt ^ 2 / kr ^ 3 + Cr * (lcnt / kr) := by ring
    have hcrude : s ≤ 2 * Cr * lcnt ^ 2 / kr ^ 3 := by
      rw [show 2 * Cr * lcnt ^ 2 / kr ^ 3 = Cr * lcnt ^ 2 / kr ^ 3 * 2 by ring]
      linarith [hSbound', hCrLine]
    have hACrude : 2 * Cr ≤ A := hACr
    let Q : ℝ := theta * lcnt ^ 2 / (s * kr ^ 3)
    have hspos : 0 < s := by
      by_contra h
      have hs0 : s = 0 := le_antisymm (le_of_not_gt h) hsnonneg
      rw [hs0] at hLarge
      have hAnontarget : 0 ≤ A * target := mul_nonneg hApos.le htargetNonneg
      linarith
    have hQpos : 0 < Q := by positivity
    have hdenBound : s * kr ^ 3 ≤ 2 * Cr * lcnt ^ 2 := by
      have hmul := (le_div_iff₀ (pow_pos hkpos 3)).mp hcrude
      field_simp [ne_of_gt hkpos] at hmul
      exact hmul
    have hthetaCr : 2 * Cr ≤ theta := by
      change 2 * Cr ≤ 4 * K + 4 * Cr + 1
      nlinarith [hKpos, hCrpos]
    have hQge : 1 ≤ Q := by
      apply (le_div_iff₀ (mul_pos hspos (pow_pos hkpos 3))).2
      have hthetaNum := mul_le_mul_of_nonneg_right hthetaCr (sq_nonneg lcnt)
      nlinarith [hdenBound, hthetaNum]
    let r : ℕ := ⌈Q⌉₊
    have hQr : Q ≤ (r : ℝ) := by dsimp [r]; exact Nat.le_ceil _
    have hRlt : (r : ℝ) < Q + 1 := by
      dsimp [r]
      exact Nat.ceil_lt_add_one hQpos.le
    have hRupper : (r : ℝ) ≤ 2 * Q := by linarith [hRlt, hQge]
    have hr1 : 1 ≤ r := by exact_mod_cast (show (1 : ℝ) ≤ (r : ℝ) by linarith)
    have hrpos : 0 < (r : ℝ) := by positivity
    obtain ⟨f, cells, hf, hdeg, hcells, hocc, hdisj, hunion, hcross⟩ :=
      hPartition S r hr1
    have hdegreeP : (f.totalDegree : ℝ) ≤ P * (r : ℝ) := hdeg
    have hcellCount : (cells.card : ℝ) ≤ P * (r : ℝ) ^ 3 := hcells
    have hcellOccupancy (R : Set (E 3)) (hR : R ∈ cells) :
        ((pointsIn S R).card : ℝ) ≤ P * s / (r : ℝ) ^ 3 := by
      simpa [s] using hocc R hR
    have hOutside :
        ((S.filter (fun x => x ∉ zeroSet f)).card : ℝ) ≤ eps * s := by
      by_contra hnot
      have hOutLarge : eps * s < (S.filter (fun x => x ∉ zeroSet f)).card := lt_of_not_ge hnot
      have hSumNat := partition_cells_cover_sample S f cells hdisj hunion
      have hSum : ((S.filter (fun x => x ∉ zeroSet f)).card : ℝ) ≤
          ∑ R ∈ cells, ((pointsIn S R).card : ℝ) := by exact_mod_cast hSumNat
      have hTotal : eps * s < ∑ R ∈ cells, ((pointsIn S R).card : ℝ) := hOutLarge.trans_le hSum
      let tau : ℝ := eps * s / (2 * P * (r : ℝ) ^ 3)
      let H : Finset (Set (E 3)) := cells.filter (fun R => tau ≤ (pointsIn S R).card)
      have htauPos : 0 < tau := by dsimp [tau]; positivity
      have hsplit : (∑ R ∈ cells, ((pointsIn S R).card : ℝ)) =
          (∑ R ∈ H, ((pointsIn S R).card : ℝ)) +
            ∑ R ∈ cells.filter (fun R => ¬ tau ≤ (pointsIn S R).card),
              ((pointsIn S R).card : ℝ) := by
        symm
        simpa [H] using
          (Finset.sum_filter_add_sum_filter_not cells
            (fun R => tau ≤ (pointsIn S R).card)
            (fun R => ((pointsIn S R).card : ℝ)))
      have hLight :
          (∑ R ∈ cells.filter (fun R => ¬ tau ≤ (pointsIn S R).card),
            ((pointsIn S R).card : ℝ)) ≤ eps * s / 2 := by
        calc
          _ ≤ ∑ R ∈ cells.filter (fun R => ¬ tau ≤ (pointsIn S R).card), tau := by
            apply Finset.sum_le_sum
            intro R hR
            exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hR).2)
          _ = ((cells.filter (fun R => ¬ tau ≤ (pointsIn S R).card)).card : ℝ) * tau := by simp
          _ ≤ (cells.card : ℝ) * tau := by
            have hfilterCard :
                (cells.filter (fun R => ¬ tau ≤ (pointsIn S R).card)).card ≤ cells.card :=
              Finset.card_le_card (Finset.filter_subset _ _)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfilterCard) htauPos.le
          _ ≤ P * (r : ℝ) ^ 3 * tau :=
            mul_le_mul_of_nonneg_right hcellCount htauPos.le
          _ = eps * s / 2 := by
            dsimp [tau]
            field_simp [ne_of_gt hPpos, ne_of_gt hspos]
            <;> ring
      have hHeavyLower : eps * s / 2 < ∑ R ∈ H, ((pointsIn S R).card : ℝ) := by
        rw [hsplit] at hTotal
        have hsumBound :
            (∑ R ∈ H, ((pointsIn S R).card : ℝ)) +
                ∑ R ∈ cells.filter (fun R => ¬ tau ≤ (pointsIn S R).card),
                  ((pointsIn S R).card : ℝ) ≤
              (∑ R ∈ H, ((pointsIn S R).card : ℝ)) + eps * s / 2 :=
          add_le_add le_rfl hLight
        have hstrict := hTotal.trans_le hsumBound
        linarith [hstrict]
      have hHeavyUpper :
          (∑ R ∈ H, ((pointsIn S R).card : ℝ)) ≤
            (H.card : ℝ) * (P * s / (r : ℝ) ^ 3) := by
        calc
          _ ≤ ∑ R ∈ H, P * s / (r : ℝ) ^ 3 := by
            apply Finset.sum_le_sum
            intro R hR
            exact hcellOccupancy R (Finset.mem_filter.mp hR).1
          _ = (H.card : ℝ) * (P * s / (r : ℝ) ^ 3) := by simp
      have hdenPos : 0 < P * s / (r : ℝ) ^ 3 := by positivity
      have hHLower : cH * (r : ℝ) ^ 3 < (H.card : ℝ) := by
        have hratio := (div_lt_iff₀ hdenPos).2 (hHeavyLower.trans_le hHeavyUpper)
        have hEq : (eps * s / 2) / (P * s / (r : ℝ) ^ 3) = cH * (r : ℝ) ^ 3 := by
          dsimp [cH, tau]
          field_simp [ne_of_gt hspos, ne_of_gt hPpos, ne_of_gt hrpos, ne_of_gt heps]
          <;> ring
        rw [hEq] at hratio
        exact hratio
      have hHpos : 0 < (H.card : ℝ) := by
        have hcHpos : 0 < cH := by dsimp [cH]; positivity
        exact lt_trans (mul_pos hcHpos (pow_pos hrpos 3)) hHLower
      have hHnonempty : H.Nonempty := by
        exact Finset.card_pos.mp (Nat.cast_pos.mp hHpos)
      let q (R : Set (E 3)) :=
        (L.filter (fun l => (R ∩ (l.1 : Set (E 3))).Nonempty)).card
      have hCrossCount : (∑ R ∈ H, q R) =
          ∑ l ∈ L, (H.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card := by
        simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
          (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := H) (t := L)
            (r := fun R l => (R ∩ (l.1 : Set (E 3))).Nonempty))
      have hlineCrossBound (l : Line 3) :
          ((H.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card : ℝ) ≤
            (f.totalDegree : ℝ) + 1 := by
        by_cases hcont : onPolynomial f l
        · have hEmpty : H.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty) = ∅ := by
            ext R
            constructor
            · intro hmem
              rcases Finset.mem_filter.mp hmem with ⟨hRH, hcrossR⟩
              rcases hcrossR with ⟨x, hx⟩
              have hxUnion : x ∈ ⋃ R ∈ cells, R := by
                simp only [Set.mem_iUnion]
                exact ⟨R, (Finset.mem_filter.mp hRH).1, hx.1⟩
              have hxComp : x ∈ (zeroSet f)ᶜ := by rw [← hunion]; exact hxUnion
              have hxEvalNe : evalR f x ≠ 0 := by simpa [zeroSet] using hxComp
              exact False.elim (hxEvalNe (hcont x hx.2))
            · intro hfalse
              simp at hfalse
          rw [hEmpty]
          simpa using (show (0 : ℝ) ≤ (f.totalDegree : ℝ) + 1 by positivity)
        · have hsubset :
              H.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty) ⊆
                cells.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty) := by
            intro R hR
            rcases Finset.mem_filter.mp hR with ⟨hRH, hcrossR⟩
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hRH).1, hcrossR⟩
          have hnat :
              (H.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card ≤ f.totalDegree + 1 := by
            calc
              _ ≤ (cells.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card :=
                Finset.card_le_card hsubset
              _ ≤ f.totalDegree + 1 := hcross l hcont
          exact_mod_cast hnat
      have hcrossSum :
          (∑ l ∈ L, ((H.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card : ℝ)) ≤
            2 * P * lcnt * (r : ℝ) := by
        calc
          _ ≤ ∑ l ∈ L, ((f.totalDegree : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro l hl
            exact hlineCrossBound l
          _ = lcnt * ((f.totalDegree : ℝ) + 1) := by simp [lcnt] <;> ring
          _ ≤ lcnt * (P * (r : ℝ) + 1) := by
            apply mul_le_mul_of_nonneg_left _ hLpos.le
            exact add_le_add hdegreeP le_rfl
          _ ≤ 2 * P * lcnt * (r : ℝ) := by
            have hrCast : 1 ≤ (r : ℝ) := by exact_mod_cast hr1
            have hPr : 1 ≤ P * (r : ℝ) := by nlinarith [hPge, hrCast]
            calc
              lcnt * (P * (r : ℝ) + 1) ≤ lcnt * (2 * P * (r : ℝ)) :=
                mul_le_mul_of_nonneg_left (by nlinarith [hPr]) hLpos.le
              _ = 2 * P * lcnt * (r : ℝ) := by ring
      have hqSum : (∑ R ∈ H, (q R : ℝ)) ≤ 2 * P * lcnt * (r : ℝ) := by
        have hCountReal : (∑ R ∈ H, (q R : ℝ)) =
            ∑ l ∈ L, ((H.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card : ℝ) := by
          exact_mod_cast hCrossCount
        rw [hCountReal]
        exact hcrossSum
      obtain ⟨R, hR, hqAverage⟩ := exists_le_real_average_plus_one
        H q hHnonempty (2 * P * lcnt * (r : ℝ)) hqSum
      have hcHpos : 0 < cH := by dsimp [cH]; positivity
      have hAvg : (2 * P * lcnt * (r : ℝ)) / (H.card : ℝ) ≤
          (2 * P / cH) * (lcnt / (r : ℝ) ^ 2) := by
        have hdenCmp : cH * (r : ℝ) ^ 3 ≤ (H.card : ℝ) := hHLower.le
        have hAvg1 : (2 * P * lcnt * (r : ℝ)) / (H.card : ℝ) ≤
            (2 * P * lcnt * (r : ℝ)) / (cH * (r : ℝ) ^ 3) := by
          apply (div_le_div_iff₀ hHpos (mul_pos hcHpos (pow_pos hrpos 3))).2
          exact mul_le_mul_of_nonneg_left hdenCmp (by positivity)
        have hAvg2 : (2 * P * lcnt * (r : ℝ)) / (cH * (r : ℝ) ^ 3) =
            (2 * P / cH) * (lcnt / (r : ℝ) ^ 2) := by
          field_simp [ne_of_gt hcHpos, ne_of_gt hrpos]
          <;> ring
        exact hAvg1.trans_eq hAvg2
      have hCcrossCoeff : 2 * P / cH ≤ Ccross := by dsimp [Ccross]; linarith
      have hLoverrNonneg : 0 ≤ lcnt / (r : ℝ) ^ 2 := by positivity
      have hscaledCoeff := mul_le_mul_of_nonneg_right hCcrossCoeff hLoverrNonneg
      have hqBound : (q R : ℝ) ≤ Ccross * (lcnt / (r : ℝ) ^ 2) + 1 := by
        calc
          (q R : ℝ) ≤ (2 * P * lcnt * (r : ℝ)) / (H.card : ℝ) + 1 := hqAverage
          _ ≤ (2 * P / cH) * (lcnt / (r : ℝ) ^ 2) + 1 := add_le_add hAvg le_rfl
          _ ≤ Ccross * (lcnt / (r : ℝ) ^ 2) + 1 := by nlinarith [hscaledCoeff]
      let Lc : Finset (Line 3) :=
        L.filter (fun l => (R ∩ (l.1 : Set (E 3))).Nonempty)
      let Xc : Finset (E 3) := pointsIn S R
      have hcellMult : ∀ x ∈ Xc, k ≤ lineMultiplicity Lc x := by
        intro x hx
        change x ∈ S.filter (fun x => x ∈ R) at hx
        rcases Finset.mem_filter.mp hx with ⟨hxS, hxR⟩
        have hbase := (hmult x hxS).1
        have hsubset : L.filter (fun l => x ∈ l.1) ⊆ Lc.filter (fun l => x ∈ l.1) := by
          intro l hl
          rcases Finset.mem_filter.mp hl with ⟨hlL, hxl⟩
          have hmemLc : l ∈ Lc := by
            dsimp [Lc]
            exact Finset.mem_filter.mpr ⟨hlL, ⟨x, ⟨hxR, hxl⟩⟩⟩
          exact Finset.mem_filter.mpr ⟨hmemLc, hxl⟩
        have hcard : lineMultiplicity L x ≤ lineMultiplicity Lc x := by
          change (L.filter (fun l => x ∈ l.1)).card ≤
            (Lc.filter (fun l => x ∈ l.1)).card
          exact Finset.card_le_card hsubset
        exact hbase.trans hcard
      have hcellIncidenceBound := (hCr 3 Xc Lc k (by omega)).1
      have hcellRichSubset : (Xc : Set (E 3)) ⊆ richPoints Lc k := by
        intro x hx
        simpa [richPoints] using hcellMult x hx
      have hcellCardNat := Set.ncard_le_ncard hcellRichSubset hcellIncidenceBound.1
      rw [Set.ncard_coe_finset] at hcellCardNat
      have hcellCardReal : (Xc.card : ℝ) ≤ (richPoints Lc k).ncard := by
        exact_mod_cast hcellCardNat
      have hcellRichBound : (Xc.card : ℝ) ≤
          Cr * ((Lc.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (Lc.card : ℝ) / k) :=
        hcellCardReal.trans hcellIncidenceBound.2
      let m : ℝ := Lc.card
      let n : ℝ := Xc.card
      have hnLower : eps * s / (2 * P * (r : ℝ) ^ 3) ≤ n := by
        have h := (Finset.mem_filter.mp hR).2
        simpa [n] using h
      have hmUpper : m ≤ Ccross * (lcnt / (r : ℝ) ^ 2) + 1 := by
        simpa [m, Lc, q] using hqBound
      let a : ℝ := Ccross * (lcnt / (r : ℝ) ^ 2)
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hmnonneg : 0 ≤ m := by
        change (0 : ℝ) ≤ (Lc.card : ℝ)
        exact_mod_cast (Nat.zero_le Lc.card)
      have hmSq : m ^ 2 ≤ 2 * Ccross ^ 2 * lcnt ^ 2 / (r : ℝ) ^ 4 + 2 := by
        have hmA : m ≤ a + 1 := by simpa [a] using hmUpper
        have hmSq' : m ^ 2 ≤ (a + 1) ^ 2 :=
          (sq_le_sq₀ hmnonneg (by positivity)).2 hmA
        have hAIdentity : a ^ 2 = Ccross ^ 2 * lcnt ^ 2 / (r : ℝ) ^ 4 := by
          dsimp [a]
          ring
        have hquad : (a + 1) ^ 2 ≤ 2 * a ^ 2 + 2 := by
          calc
            (a + 1) ^ 2 = 2 * a ^ 2 + 2 - (a - 1) ^ 2 := by ring
            _ ≤ 2 * a ^ 2 + 2 := sub_le_self _ (sq_nonneg (a - 1))
        calc
          m ^ 2 ≤ (a + 1) ^ 2 := hmSq'
          _ ≤ 2 * a ^ 2 + 2 := hquad
          _ = 2 * Ccross ^ 2 * lcnt ^ 2 / (r : ℝ) ^ 4 + 2 := by
            calc
              2 * a ^ 2 + 2 = 2 * (Ccross ^ 2 * lcnt ^ 2 / (r : ℝ) ^ 4) + 2 :=
                congrArg (fun z : ℝ => 2 * z + 2) hAIdentity
              _ = 2 * Ccross ^ 2 * lcnt ^ 2 / (r : ℝ) ^ 4 + 2 := by ring
      have hmDiv : m / kr ≤ Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 1 / kr := by
        have hmDiv' := div_le_div_of_nonneg_right hmUpper hkpos.le
        calc
          m / kr ≤ (Ccross * (lcnt / (r : ℝ) ^ 2) + 1) / kr := hmDiv'
          _ = Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 1 / kr := by
            field_simp [ne_of_gt hkpos, ne_of_gt hrpos]
            <;> ring
      have hkNatOne : 1 ≤ k := by omega
      have hkrone : 1 ≤ kr := by
        dsimp [kr]
        exact_mod_cast hkNatOne
      have hkrCube : kr ≤ kr ^ 3 := by
        calc
          kr = kr * 1 := by ring
          _ ≤ kr * kr ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hkrone) hkpos.le
          _ = kr ^ 3 := by ring
      have hInvCube : 1 / kr ^ 3 ≤ 1 / kr := by
        apply (div_le_div_iff₀ (pow_pos hkpos 3) hkpos).2
        simpa only [one_mul] using hkrCube
      have hTwoInvCube : 2 / kr ^ 3 ≤ 2 / kr := by
        calc
          2 / kr ^ 3 = 2 * (1 / kr ^ 3) := by ring
          _ ≤ 2 * (1 / kr) := mul_le_mul_of_nonneg_left hInvCube (by norm_num)
          _ = 2 / kr := by ring
      have hsmallTerms : 2 / kr ^ 3 + 1 / kr ≤ 3 / kr := by
        calc
          2 / kr ^ 3 + 1 / kr ≤ 2 / kr + 1 / kr := add_le_add hTwoInvCube le_rfl
          _ = 3 / kr := by ring
      have hcellSumBound : m ^ 2 / kr ^ 3 + m / kr ≤
          2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3) +
            Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 3 / kr := by
        calc
          _ ≤ (2 * Ccross ^ 2 * lcnt ^ 2 / (r : ℝ) ^ 4 + 2) / kr ^ 3 +
                (Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 1 / kr) := by
              have hsqDiv : m ^ 2 / kr ^ 3 ≤
                  (2 * Ccross ^ 2 * lcnt ^ 2 / (r : ℝ) ^ 4 + 2) / kr ^ 3 :=
                div_le_div_of_nonneg_right hmSq (show 0 ≤ kr ^ 3 by positivity)
              exact add_le_add hsqDiv hmDiv
          _ = 2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3) +
                Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + (2 / kr ^ 3 + 1 / kr) := by
              field_simp [ne_of_gt hkpos, ne_of_gt hrpos]
              <;> ring
          _ ≤ 2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3) +
                Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 3 / kr := by
              exact add_le_add le_rfl hsmallTerms
      have hcellRichBound' : n ≤ Cr * (m ^ 2 / kr ^ 3 + m / kr) := by
        simpa only [n, m, kr] using hcellRichBound
      have hcellRichBound'' : n ≤ Cr *
          (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3) +
            Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 3 / kr) := by
        calc
          n ≤ Cr * (m ^ 2 / kr ^ 3 + m / kr) := hcellRichBound'
          _ ≤ Cr * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3) +
                Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 3 / kr) :=
            mul_le_mul_of_nonneg_left hcellSumBound hCrpos.le
      have hscalePos : 0 < 2 * P * (r : ℝ) ^ 3 / eps := by positivity
      have hscaledLower : eps * s ≤ n * (2 * P * (r : ℝ) ^ 3) :=
        (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hPpos) (pow_pos hrpos 3))).mp hnLower
      have hscaled : s ≤ (2 * P * (r : ℝ) ^ 3 / eps) * n := by
        have hscaleEq : (2 * P * (r : ℝ) ^ 3 / eps) * n =
            (2 * P * (r : ℝ) ^ 3 * n) / eps := by ring
        rw [hscaleEq]
        apply (le_div_iff₀ heps).2
        calc
          s * eps = eps * s := by ring
          _ ≤ n * (2 * P * (r : ℝ) ^ 3) := hscaledLower
          _ = 2 * P * (r : ℝ) ^ 3 * n := by ring
      have hscaleUpper : s ≤ (2 * P * (r : ℝ) ^ 3 / eps) *
          (Cr * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3) +
            Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 3 / kr)) := by
        exact hscaled.trans (mul_le_mul_of_nonneg_left hcellRichBound'' hscalePos.le)
      let hcoeff : ℝ := 2 * P * Cr / eps
      have hscaleA : (2 * P * (r : ℝ) ^ 3 / eps) *
          (Cr * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3))) =
          hcoeff * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) * kr ^ 3)) := by
        dsimp [hcoeff]
        field_simp [ne_of_gt heps, ne_of_gt hrpos, ne_of_gt hkpos]
        <;> ring
      have hscaleB : (2 * P * (r : ℝ) ^ 3 / eps) *
          (Cr * (Ccross * lcnt / ((r : ℝ) ^ 2 * kr))) =
          hcoeff * (Ccross * lcnt * (r : ℝ) / kr) := by
        dsimp [hcoeff]
        field_simp [ne_of_gt heps, ne_of_gt hrpos, ne_of_gt hkpos]
        <;> ring
      have hscaleC : (2 * P * (r : ℝ) ^ 3 / eps) * (Cr * (3 / kr)) =
          hcoeff * (3 * (r : ℝ) ^ 3 / kr) := by
        dsimp [hcoeff]
        field_simp [ne_of_gt heps, ne_of_gt hrpos, ne_of_gt hkpos]
        <;> ring
      have hscaleRewrite : (2 * P * (r : ℝ) ^ 3 / eps) *
          (Cr * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3) +
            Ccross * lcnt / ((r : ℝ) ^ 2 * kr) + 3 / kr)) =
          hcoeff * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) * kr ^ 3) +
            Ccross * lcnt * (r : ℝ) / kr + 3 * (r : ℝ) ^ 3 / kr) := by
        calc
          _ = (2 * P * (r : ℝ) ^ 3 / eps) * (Cr *
                (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) ^ 4 * kr ^ 3))) +
              (2 * P * (r : ℝ) ^ 3 / eps) * (Cr *
                (Ccross * lcnt / ((r : ℝ) ^ 2 * kr))) +
              (2 * P * (r : ℝ) ^ 3 / eps) * (Cr * (3 / kr)) := by ring
          _ = hcoeff * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) * kr ^ 3)) +
              hcoeff * (Ccross * lcnt * (r : ℝ) / kr) +
              hcoeff * (3 * (r : ℝ) ^ 3 / kr) := by rw [hscaleA, hscaleB, hscaleC]
          _ = _ := by ring
      let aTerm : ℝ := lcnt ^ 2 / ((r : ℝ) * kr ^ 3)
      let bTerm : ℝ := lcnt * (r : ℝ) / kr
      let cTerm : ℝ := (r : ℝ) ^ 3 / kr
      have haTerm : 0 ≤ aTerm := by
        dsimp [aTerm]
        exact div_nonneg (sq_nonneg lcnt) (mul_nonneg hrpos.le (pow_nonneg hkpos.le 3))
      have hbTerm : 0 ≤ bTerm := by
        dsimp [bTerm]
        exact div_nonneg (mul_nonneg hLpos.le hrpos.le) hkpos.le
      have hcTerm : 0 ≤ cTerm := by
        dsimp [cTerm]
        exact div_nonneg (pow_nonneg hrpos.le 3) hkpos.le
      have hsumCoef : 2 * Ccross ^ 2 * aTerm + Ccross * bTerm + 3 * cTerm ≤
          (2 * Ccross ^ 2 + Ccross + 3) * (aTerm + bTerm + cTerm) := by
        have hCcrossNonneg : 0 ≤ Ccross := by positivity
        have hcoefA : 2 * Ccross ^ 2 ≤ 2 * Ccross ^ 2 + Ccross + 3 := by
          calc
            2 * Ccross ^ 2 ≤ 2 * Ccross ^ 2 + (Ccross + 3) :=
              le_add_of_nonneg_right (add_nonneg hCcrossNonneg (by norm_num))
            _ = 2 * Ccross ^ 2 + Ccross + 3 := by ring
        have hcoefB : Ccross ≤ 2 * Ccross ^ 2 + Ccross + 3 := by
          calc
            Ccross ≤ Ccross + (2 * Ccross ^ 2 + 3) :=
              le_add_of_nonneg_right (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg Ccross))
                (by norm_num))
            _ = 2 * Ccross ^ 2 + Ccross + 3 := by ring
        have hcoefC : 3 ≤ 2 * Ccross ^ 2 + Ccross + 3 := by
          calc
            3 ≤ 3 + (2 * Ccross ^ 2 + Ccross) :=
              le_add_of_nonneg_right
                (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg Ccross)) hCcrossNonneg)
            _ = 2 * Ccross ^ 2 + Ccross + 3 := by ring
        calc
          _ ≤ (2 * Ccross ^ 2 + Ccross + 3) * aTerm +
              (2 * Ccross ^ 2 + Ccross + 3) * bTerm +
              (2 * Ccross ^ 2 + Ccross + 3) * cTerm := by
            exact add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_right hcoefA haTerm)
                (mul_le_mul_of_nonneg_right hcoefB hbTerm))
              (mul_le_mul_of_nonneg_right hcoefC hcTerm)
          _ = (2 * Ccross ^ 2 + Ccross + 3) * (aTerm + bTerm + cTerm) := by ring
      have hcellTerms : s ≤ K * (aTerm + bTerm + cTerm) := by
        have hsumEq :
            2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) * kr ^ 3) +
              Ccross * lcnt * (r : ℝ) / kr + 3 * (r : ℝ) ^ 3 / kr =
            2 * Ccross ^ 2 * aTerm + Ccross * bTerm + 3 * cTerm := by
          dsimp [aTerm, bTerm, cTerm]
          ring
        have hscaleUpper' : s ≤ hcoeff *
            (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) * kr ^ 3) +
              Ccross * lcnt * (r : ℝ) / kr + 3 * (r : ℝ) ^ 3 / kr) :=
          hscaleUpper.trans_eq hscaleRewrite
        calc
          s ≤ hcoeff * (2 * Ccross ^ 2 * aTerm + Ccross * bTerm + 3 * cTerm) := by
            calc
              s ≤ hcoeff * (2 * Ccross ^ 2 * lcnt ^ 2 / ((r : ℝ) * kr ^ 3) +
                    Ccross * lcnt * (r : ℝ) / kr + 3 * (r : ℝ) ^ 3 / kr) := hscaleUpper'
              _ = hcoeff * (2 * Ccross ^ 2 * aTerm + Ccross * bTerm + 3 * cTerm) := by
                rw [hsumEq]
          _ ≤ hcoeff * ((2 * Ccross ^ 2 + Ccross + 3) *
              (aTerm + bTerm + cTerm)) :=
            mul_le_mul_of_nonneg_left hsumCoef (by positivity)
          _ = K * (aTerm + bTerm + cTerm) := by dsimp [K, hcoeff]; ring
      have hcell : s ≤ K *
          (lcnt ^ 2 / ((r : ℝ) * kr ^ 3) + lcnt * (r : ℝ) / kr + (r : ℝ) ^ 3 / kr) := by
        change s ≤ K * (aTerm + bTerm + cTerm)
        exact hcellTerms
      have hpow : (lcnt ^ ((3 : ℝ) / 2) / kr ^ 2) ^ 2 = lcnt ^ 3 / kr ^ 4 := by
        have hpowL : (lcnt ^ ((3 : ℝ) / 2)) ^ 2 = lcnt ^ 3 := by
          rw [← Real.rpow_mul_natCast hLpos.le ((3 : ℝ) / 2) 2]
          norm_num [Real.rpow_natCast]
        rw [div_pow, hpowL]
        ring
      have hthetaPos : 0 < theta := by dsimp [theta]; positivity
      have hAK4le : AK4 ≤ A := by
        calc
          AK4 ≤ max AK4 Ares := le_max_left _ _
          _ ≤ max AK (max AK4 Ares) := le_max_right _ _
          _ ≤ max Atheta (max AK (max AK4 Ares)) := le_max_right _ _
          _ ≤ A := le_max_right _ _
      have hAK4one : 1 ≤ AK4 := by
        change 1 ≤ 32 * K * theta ^ 3 + 1
        have hterm : 0 ≤ 32 * K * theta ^ 3 :=
          mul_nonneg (mul_nonneg (by norm_num) hKpos.le) (pow_nonneg hthetaPos.le 3)
        calc
          1 ≤ 1 + 32 * K * theta ^ 3 := le_add_of_nonneg_right hterm
          _ = 32 * K * theta ^ 3 + 1 := by ring
      have hAone : 1 ≤ A := hAK4one.trans hAK4le
      have hAKle : AK ≤ A := by
        calc
          AK ≤ max AK (max AK4 Ares) := le_max_left _ _
          _ ≤ max Atheta (max AK (max AK4 Ares)) := le_max_right _ _
          _ ≤ A := le_max_right _ _
      have hA8 : 8 * K * theta ≤ A := by dsimp [AK] at hAKle; linarith
      have hAres : 6 * P * theta / eps ≤ A := by
        have hAresle : Ares ≤ A := by
          calc
            Ares ≤ max AK4 Ares := le_max_right _ _
            _ ≤ max AK (max AK4 Ares) := le_max_right _ _
            _ ≤ max Atheta (max AK (max AK4 Ares)) := le_max_right _ _
            _ ≤ A := le_max_right _ _
        dsimp [Ares] at hAresle
        linarith
      have hThetaGe : 4 * K ≤ theta := by
        change 4 * K ≤ 4 * K + 4 * Cr + 1
        calc
          4 * K ≤ 4 * K + (4 * Cr + 1) :=
            le_add_of_nonneg_right (by positivity : 0 ≤ 4 * Cr + 1)
          _ = 4 * K + 4 * Cr + 1 := by ring
      have hKover4 : K ≤ theta / 4 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
        simpa [mul_comm] using hThetaGe
      have hKtheta : K / theta ≤ 1 / 4 := by
        rw [div_le_iff₀ hthetaPos]
        calc
          K ≤ theta / 4 := hKover4
          _ = 1 / 4 * theta := by ring
      have hKA : 2 * K * theta / A ≤ 1 / 4 := by
        have hdiv : (8 * K * theta) / A ≤ 1 := (div_le_one hApos).2 hA8
        calc
          2 * K * theta / A = ((8 * K * theta) / A) / 4 := by ring
          _ ≤ 1 / 4 := div_le_div_of_nonneg_right hdiv (by norm_num : 0 ≤ (4 : ℝ))
      have hAK4plus : 32 * K * theta ^ 3 + 1 ≤ A := by
        simpa only [AK4] using hAK4le
      have hA4succ : 32 * K * theta ^ 3 ≤ 32 * K * theta ^ 3 + 1 := by
        have h01 : (0 : ℝ) ≤ 1 := by norm_num
        simpa using (add_le_add_left h01 (32 * K * theta ^ 3))
      have hA4base : 32 * K * theta ^ 3 ≤ A := hA4succ.trans hAK4plus
      have hA3 : 1 ≤ A ^ 3 := one_le_pow₀ hAone
      have hA4pow : A ≤ A ^ 4 := by
        calc
          A = A * 1 := by ring
          _ ≤ A * A ^ 3 := mul_le_mul_of_nonneg_left hA3 hApos.le
          _ = A ^ 4 := by ring
      have hA4 : 32 * K * theta ^ 3 ≤ A ^ 4 := hA4base.trans hA4pow
      have hKA4 : 8 * K * theta ^ 3 / A ^ 4 ≤ 1 / 4 := by
        apply (div_le_iff₀ (pow_pos hApos 4)).2
        calc
          8 * K * theta ^ 3 = (32 * K * theta ^ 3) / 4 := by ring
          _ ≤ A ^ 4 / 4 := div_le_div_of_nonneg_right hA4 (by norm_num : 0 ≤ (4 : ℝ))
          _ = (1 / 4) * A ^ 4 := by ring
      have hkge1 : 1 ≤ kr := by
        change (1 : ℝ) ≤ (k : ℝ)
        exact_mod_cast (show 1 ≤ k by omega)
      have hQr' : theta * lcnt ^ 2 / (s * kr ^ 3) ≤ (r : ℝ) := by
        simpa only [Q] using hQr
      have hRupper' : (r : ℝ) ≤ 2 * theta * lcnt ^ 2 / (s * kr ^ 3) := by
        calc
          (r : ℝ) ≤ 2 * Q := hRupper
          _ = 2 * theta * lcnt ^ 2 / (s * kr ^ 3) := by dsimp [Q]; ring
      have hLarge' : A * (lcnt ^ ((3 : ℝ) / 2) / kr ^ 2 + lcnt / kr) < s := by
        simpa [target] using hLarge
      exact False.elim (no_large_partition_solution hLpos hspos hkpos
        hkge1 hrpos hthetaPos hApos hAone (le_of_lt hKpos) hpow hQr' hRupper' hLarge'
        hKtheta hKA hKA4 hcell)
    obtain ⟨g, hg, hgsq, hgdeg, hgzero⟩ := squarefree_part f hf
    have hD : (g.totalDegree : ℝ) ≤ P * (r : ℝ) := by
      have hdeg' : (g.totalDegree : ℝ) ≤ (f.totalDegree : ℝ) := by exact_mod_cast hgdeg
      exact hdeg'.trans hdegreeP
    have hOutsideG : ((S.filter (fun x => x ∉ zeroSet g)).card : ℝ) ≤ eps * s := by
      simpa [hgzero] using hOutside
    let Lz : Finset (Line 3) := L.filter (fun l => onPolynomial g l)
    let Lout : Finset (Line 3) := L.filter (fun l => ¬ onPolynomial g l)
    let Sstar : Finset (E 3) := S.filter (fun x => x ∈ zeroSet g ∧ 3 ≤ lineMultiplicity Lz x)
    let SbadZ : Finset (E 3) := S.filter (fun x => x ∈ zeroSet g ∧ lineMultiplicity Lz x < 3)
    let SoutG : Finset (E 3) := S.filter (fun x => x ∉ zeroSet g)
    have hresidual := polynomial_zero_residual_bound g S L k hk
      (fun x hx => (hmult x hx).1)
    have hresidualNat : SbadZ.card * (k - 2) ≤ L.card * g.totalDegree := by
      simpa [Lz, Lout, SbadZ] using hresidual
    have hkCast : (3 : ℝ) ≤ kr := by
      change (3 : ℝ) ≤ (k : ℝ)
      exact_mod_cast hk
    have hkmCast : ((k - 2 : ℕ) : ℝ) = kr - 2 := by
      dsimp [kr]
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hkmThird : kr / 3 ≤ ((k - 2 : ℕ) : ℝ) := by
      rw [hkmCast]
      linarith
    have hresidualReal : (SbadZ.card : ℝ) * ((k - 2 : ℕ) : ℝ) ≤
        lcnt * (g.totalDegree : ℝ) := by
      change (SbadZ.card : ℝ) * ((k - 2 : ℕ) : ℝ) ≤ (L.card : ℝ) * (g.totalDegree : ℝ)
      exact_mod_cast hresidualNat
    have hbadMultBound : (SbadZ.card : ℝ) ≤
        3 * lcnt * (g.totalDegree : ℝ) / kr := by
      have hmul := mul_le_mul_of_nonneg_left hkmThird (Nat.cast_nonneg SbadZ.card)
      have hcount : (SbadZ.card : ℝ) * kr ≤ 3 * lcnt * (g.totalDegree : ℝ) := by
        have h := hmul.trans hresidualReal
        nlinarith [h]
      exact (le_div_iff₀ hkpos).2 hcount
    have hSbadSubset :
        S.filter (fun x => x ∉ Sstar) ⊆ SbadZ ∪ SoutG := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxS, hxNotStar⟩
      by_cases hxZero : x ∈ zeroSet g
      · have hLzlt : lineMultiplicity Lz x < 3 := by
          by_contra hnot
          have hthree : 3 ≤ lineMultiplicity Lz x := le_of_not_gt hnot
          exact hxNotStar (Finset.mem_filter.mpr ⟨hxS, ⟨hxZero, hthree⟩⟩)
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hxS, ⟨hxZero, hLzlt⟩⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxS, hxZero⟩))
    have hSbadCard : (S.filter (fun x => x ∉ Sstar)).card ≤ SbadZ.card + SoutG.card := by
      calc
        _ ≤ (SbadZ ∪ SoutG).card := Finset.card_le_card hSbadSubset
        _ ≤ SbadZ.card + SoutG.card := Finset.card_union_le _ _
    have hSbadReal : ((S.filter (fun x => x ∉ Sstar)).card : ℝ) ≤
        (SbadZ.card : ℝ) + (SoutG.card : ℝ) := by exact_mod_cast hSbadCard
    have hSoutBound : (SoutG.card : ℝ) ≤ eps * s := by
      simpa [SoutG] using hOutsideG
    have hRupperFinal : (r : ℝ) ≤ 2 * theta * lcnt ^ 2 / (s * kr ^ 3) := by
      calc
        (r : ℝ) ≤ 2 * Q := hRupper
        _ = 2 * theta * lcnt ^ 2 / (s * kr ^ 3) := by dsimp [Q]; ring
    have hDsmall : (g.totalDegree : ℝ) ≤ 2 * P * theta * lcnt ^ 2 / (s * kr ^ 3) := by
      calc
        (g.totalDegree : ℝ) ≤ P * (r : ℝ) := hD
        _ ≤ P * (2 * theta * lcnt ^ 2 / (s * kr ^ 3)) :=
          mul_le_mul_of_nonneg_left hRupperFinal hPpos.le
        _ = 2 * P * theta * lcnt ^ 2 / (s * kr ^ 3) := by ring
    have hpow : (lcnt ^ ((3 : ℝ) / 2) / kr ^ 2) ^ 2 = lcnt ^ 3 / kr ^ 4 := by
      have hpowL : (lcnt ^ ((3 : ℝ) / 2)) ^ 2 = lcnt ^ 3 := by
        rw [← Real.rpow_mul_natCast hLpos.le ((3 : ℝ) / 2) 2]
        norm_num [Real.rpow_natCast]
      rw [div_pow, hpowL]
      ring
    let u : ℝ := lcnt ^ ((3 : ℝ) / 2) / kr ^ 2
    have hu : 0 < u := by dsimp [u]; positivity
    have hmainLarge : A * u < s := by
      have htargetLower : u ≤ target := by
        dsimp [u, target]
        exact le_add_of_nonneg_right (div_nonneg hLpos.le hkpos.le)
      have hmul := mul_le_mul_of_nonneg_left htargetLower hApos.le
      dsimp [u] at hmul
      linarith [hLarge]
    have huSmall : u < s / A := (lt_div_iff₀ hApos).2 (by simpa [mul_comm] using hmainLarge)
    have hu2 : u ^ 2 ≤ s ^ 2 / A ^ 2 := by
      calc
        u ^ 2 ≤ (s / A) ^ 2 := pow_le_pow_left₀ hu.le huSmall.le 2
        _ = s ^ 2 / A ^ 2 := by ring
    have hRatioPow : lcnt ^ 3 / (s * kr ^ 4) = u ^ 2 / s := by
      dsimp [u]
      calc
        lcnt ^ 3 / (s * kr ^ 4) = (lcnt ^ 3 / kr ^ 4) / s := by
          field_simp [ne_of_gt hspos, ne_of_gt hkpos]
          <;> ring
        _ = (lcnt ^ ((3 : ℝ) / 2) / kr ^ 2) ^ 2 / s := by rw [← hpow]
    have hRatioBound : lcnt ^ 3 / (s * kr ^ 4) ≤ s / A ^ 2 := by
      rw [hRatioPow]
      calc
        u ^ 2 / s ≤ (s ^ 2 / A ^ 2) / s := div_le_div_of_nonneg_right hu2 hspos.le
        _ = s / A ^ 2 := by field_simp [ne_of_gt hspos] <;> ring
    have hbadDegreeBound : (SbadZ.card : ℝ) ≤
        6 * P * theta * lcnt ^ 3 / (s * kr ^ 4) := by
      have hmul := mul_le_mul_of_nonneg_left hDsmall (by positivity : 0 ≤ 3 * lcnt)
      calc
        (SbadZ.card : ℝ) ≤ 3 * lcnt * (g.totalDegree : ℝ) / kr := hbadMultBound
        _ ≤ 3 * lcnt * (2 * P * theta * lcnt ^ 2 / (s * kr ^ 3)) / kr := by
          exact div_le_div_of_nonneg_right hmul hkpos.le
        _ = 6 * P * theta * lcnt ^ 3 / (s * kr ^ 4) := by
          field_simp [ne_of_gt hspos, ne_of_gt hkpos]
          <;> ring
    have hAresle : 6 * P * theta / eps ≤ A := by
      have hAresBound : Ares ≤ A := by
        calc
          Ares ≤ max AK4 Ares := le_max_right _ _
          _ ≤ max AK (max AK4 Ares) := le_max_right _ _
          _ ≤ max Atheta (max AK (max AK4 Ares)) := le_max_right _ _
          _ ≤ A := le_max_right _ _
      dsimp [Ares] at hAresBound
      linarith
    have hAone : 1 ≤ A := by
      have hACrOne : 1 ≤ ACr := by dsimp [ACr]; linarith [hCrpos]
      exact hACrOne.trans (le_max_left _ _)
    have h6Ptheta : 6 * P * theta ≤ eps * A := by
      have h := (div_le_iff₀ heps).mp hAresle
      simpa [mul_comm] using h
    have hA2 : A ≤ A ^ 2 := by
      calc
        A = A * 1 := by ring
        _ ≤ A * A := mul_le_mul_of_nonneg_left hAone hApos.le
        _ = A ^ 2 := by ring
    have hRatioCoeff : 6 * P * theta / A ^ 2 ≤ eps := by
      apply (div_le_iff₀ (sq_pos_of_pos hApos)).2
      exact le_trans h6Ptheta (mul_le_mul_of_nonneg_left hA2 heps.le)
    have hbadFinal : (SbadZ.card : ℝ) ≤ eps * s := by
      calc
        (SbadZ.card : ℝ) ≤ 6 * P * theta * lcnt ^ 3 / (s * kr ^ 4) := hbadDegreeBound
        _ = (6 * P * theta) * (lcnt ^ 3 / (s * kr ^ 4)) := by ring
        _ ≤ (6 * P * theta) * (s / A ^ 2) :=
          mul_le_mul_of_nonneg_left hRatioBound (by positivity)
        _ = (6 * P * theta / A ^ 2) * s := by ring
        _ ≤ eps * s := mul_le_mul_of_nonneg_right hRatioCoeff hspos.le
    let SnotStar : Finset (E 3) := S.filter (fun x => x ∉ Sstar)
    have hSnotStarBound : (SnotStar.card : ℝ) ≤ 2 * eps * s := by
      have h : (SnotStar.card : ℝ) ≤ (SbadZ.card : ℝ) + (SoutG.card : ℝ) := by
        simpa [SnotStar] using hSbadReal
      calc
        (SnotStar.card : ℝ) ≤ (SbadZ.card : ℝ) + (SoutG.card : ℝ) := h
        _ ≤ eps * s + eps * s := add_le_add hbadFinal hSoutBound
        _ = 2 * eps * s := by ring
    let Lbase : Finset (Line 3) := L.filter
      (fun l => s * kr / (100 * lcnt) ≤ (pointsOn S l).card)
    have hbase : lcnt / 100 ≤ (Lbase.card : ℝ) := by
      simpa [Lbase, s, kr, lcnt] using huniform
    let tau : ℝ := s * kr / (200 * lcnt)
    have htauPos : 0 < tau := by dsimp [tau]; positivity
    let Rline (l : Line 3) : Finset (E 3) :=
      (pointsOn S l).filter (fun x => x ∉ Sstar)
    have hRline (l : Line 3) : Rline l = SnotStar.filter (fun x => x ∈ l.1) := by
      ext x
      simp [Rline, SnotStar, pointsOn, Finset.filter_filter,
        and_assoc, and_left_comm, and_comm]
    have hcountEq : (∑ l ∈ Lbase, (Rline l).card) =
        ∑ x ∈ SnotStar, (Lbase.filter (fun l => x ∈ l.1)).card := by
      simp_rw [hRline]
      simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := Lbase) (t := SnotStar) (r := fun l x => x ∈ l.1))
    have hsumNat : (∑ l ∈ Lbase, (Rline l).card) ≤ SnotStar.card * (2 * k) := by
      rw [hcountEq]
      calc
        _ ≤ ∑ x ∈ SnotStar, (2 * k) := by
          apply Finset.sum_le_sum
          intro x hx
          have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
          have hsub : Lbase.filter (fun l => x ∈ l.1) ⊆ L.filter (fun l => x ∈ l.1) := by
            intro l hl
            rcases Finset.mem_filter.mp hl with ⟨hlbase, hxl⟩
            exact Finset.mem_filter.mpr ⟨(Finset.filter_subset _ _) hlbase, hxl⟩
          have hcard := Finset.card_le_card hsub
          have hupper := (hmult x hxS).2
          unfold lineMultiplicity at hupper
          omega
        _ = SnotStar.card * (2 * k) := by simp
    have hsumTotal : (∑ l ∈ Lbase, ((Rline l).card : ℝ)) ≤ 4 * eps * kr * s := by
      have hsumCast : (∑ l ∈ Lbase, ((Rline l).card : ℝ)) ≤
          (SnotStar.card : ℝ) * (2 * kr) := by
        have hcast : (((∑ l ∈ Lbase, (Rline l).card) : ℕ) : ℝ) ≤
            ((SnotStar.card * (2 * k) : ℕ) : ℝ) := by exact_mod_cast hsumNat
        have hcast' : (∑ l ∈ Lbase, ((Rline l).card : ℝ)) ≤
            (SnotStar.card : ℝ) * (2 * kr) := by
          simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, kr] using hcast
        exact hcast'
      calc
        _ ≤ (SnotStar.card : ℝ) * (2 * kr) := hsumCast
        _ ≤ (2 * eps * s) * (2 * kr) :=
          mul_le_mul_of_nonneg_right hSnotStarBound (by positivity)
        _ = 4 * eps * kr * s := by ring
    let Lbad : Finset (Line 3) := Lbase.filter (fun l => tau ≤ (Rline l).card)
    let Lgood : Finset (Line 3) := Lbase.filter (fun l => ¬ tau ≤ (Rline l).card)
    have hsumSplit : (∑ l ∈ Lbase, ((Rline l).card : ℝ)) =
        (∑ l ∈ Lbad, ((Rline l).card : ℝ)) +
          ∑ l ∈ Lgood, ((Rline l).card : ℝ) := by
      simpa [Lbad, Lgood] using
        (Finset.sum_filter_add_sum_filter_not Lbase
          (fun l => tau ≤ (Rline l).card) (fun l => ((Rline l).card : ℝ))).symm
    have hsumBadLower : (Lbad.card : ℝ) * tau ≤
        ∑ l ∈ Lbase, ((Rline l).card : ℝ) := by
      calc
        (Lbad.card : ℝ) * tau = ∑ l ∈ Lbad, tau := by simp [mul_comm]
        _ ≤ ∑ l ∈ Lbad, ((Rline l).card : ℝ) := by
          apply Finset.sum_le_sum
          intro l hl
          exact (Finset.mem_filter.mp hl).2
        _ ≤ ∑ l ∈ Lbase, ((Rline l).card : ℝ) := by
          rw [hsumSplit]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    have hbadBound : (Lbad.card : ℝ) ≤ 800 * eps * lcnt := by
      have hratio : (Lbad.card : ℝ) * (s * kr) / (200 * lcnt) ≤
          4 * eps * kr * s := by
        calc
          _ = (Lbad.card : ℝ) * tau := by dsimp [tau]; ring
          _ ≤ ∑ l ∈ Lbase, ((Rline l).card : ℝ) := hsumBadLower
          _ ≤ 4 * eps * kr * s := hsumTotal
      have hmultiplied := (div_le_iff₀ (by positivity : 0 < 200 * lcnt)).mp hratio
      have hmulBound : (Lbad.card : ℝ) * (s * kr) ≤
          (800 * eps * lcnt) * (s * kr) := by
        calc
          _ ≤ (4 * eps * kr * s) * (200 * lcnt) := hmultiplied
          _ = (800 * eps * lcnt) * (s * kr) := by ring
      have hpos : 0 < s * kr := mul_pos hspos hkpos
      have hquot := (div_le_div_iff₀ hpos hpos).2 hmulBound
      have hcancel : (Lbad.card : ℝ) ≤ 800 * eps * lcnt := by
        field_simp [ne_of_gt hpos] at hquot
        exact hquot
      exact hcancel
    have hbaseSplit : Lbase.card = Lbad.card + Lgood.card := by
      simpa [Lbad, Lgood] using
        (Lbase.card_filter_add_card_filter_not (fun l => tau ≤ (Rline l).card)).symm
    have hgoodBound : lcnt / 200 ≤ (Lgood.card : ℝ) := by
      have hsplitReal : (Lbase.card : ℝ) = (Lbad.card : ℝ) + (Lgood.card : ℝ) := by
        exact_mod_cast hbaseSplit
      have hrough : lcnt / 100 - 800 * eps * lcnt ≤ (Lgood.card : ℝ) := by
        have hbase' := hbase
        rw [hsplitReal] at hbase'
        rw [sub_le_iff_le_add]
        calc
          lcnt / 100 ≤ (Lbad.card : ℝ) + (Lgood.card : ℝ) := hbase'
          _ ≤ 800 * eps * lcnt + (Lgood.card : ℝ) :=
            add_le_add hbadBound (le_refl _)
          _ = (Lgood.card : ℝ) + 800 * eps * lcnt := by ring
      have hcoeff : (1 : ℝ) / 200 ≤ 1 / 100 - 800 * eps := by norm_num [eps]
      have hscaled := mul_le_mul_of_nonneg_right hcoeff hLpos.le
      calc
        lcnt / 200 ≤ (1 / 100 - 800 * eps) * lcnt := by nlinarith [hscaled]
        _ = lcnt / 100 - 800 * eps * lcnt := by ring
        _ ≤ (Lgood.card : ℝ) := hrough
    have hStarOnGood (l : Line 3) (hl : l ∈ Lgood) :
        tau ≤ (((pointsOn S l).filter (fun x => x ∈ Sstar)).card : ℝ) := by
      have hlbase : l ∈ Lbase := (Finset.filter_subset _ _) hl
      have hlarge := (Finset.mem_filter.mp hlbase).2
      have hlarge' : 2 * tau ≤ (pointsOn S l).card := by
        have heq : 2 * tau = s * kr / (100 * lcnt) := by dsimp [tau]; ring
        rw [heq]
        exact hlarge
      have hsmall : ((Rline l).card : ℝ) < tau := by
        have h := (Finset.mem_filter.mp hl).2
        exact lt_of_not_ge h
      have hsplitNat :
          ((pointsOn S l).filter (fun x => x ∈ Sstar)).card +
            (Rline l).card = (pointsOn S l).card := by
        have h := (pointsOn S l).card_filter_add_card_filter_not (fun x => x ∈ Sstar)
        simpa [Rline, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using h
      have hsplitReal :
          (((pointsOn S l).filter (fun x => x ∈ Sstar)).card : ℝ) +
            (Rline l).card = (pointsOn S l).card := by exact_mod_cast hsplitNat
      nlinarith [hlarge', hsmall, hsplitReal]
    have hRatioCritical : lcnt ^ 3 / (s ^ 2 * kr ^ 4) ≤ 1 / A ^ 2 := by
      calc
        lcnt ^ 3 / (s ^ 2 * kr ^ 4) = (lcnt ^ 3 / (s * kr ^ 4)) / s := by
          field_simp [ne_of_gt hspos, ne_of_gt hkpos]
          <;> ring
        _ ≤ (s / A ^ 2) / s := div_le_div_of_nonneg_right hRatioBound hspos.le
        _ = 1 / A ^ 2 := by field_simp [ne_of_gt hspos] <;> ring
    have hthetaPos : 0 < theta := by dsimp [theta]; positivity
    have hPthetaPos : 0 < P * theta := mul_pos hPpos hthetaPos
    have hAcritical : 2400 * P * theta < A := by
      have hcoeff : (2400 : ℝ) < 6 / eps := by norm_num [eps]
      have hmul := mul_lt_mul_of_pos_right hcoeff hPthetaPos
      have hscale : 2400 * P * theta < 6 * P * theta / eps := by
        calc
          2400 * P * theta = 2400 * (P * theta) := by ring
          _ < (6 / eps) * (P * theta) := hmul
          _ = 6 * P * theta / eps := by ring
      exact hscale.trans_le hAresle
    have hAcriticalSq : 2400 * P * theta < A ^ 2 := hAcritical.trans_le hA2
    have hcriticalCoeff : 2400 * P * theta / A ^ 2 < 1 := by
      apply (div_lt_iff₀ (sq_pos_of_pos hApos)).2
      nlinarith [hAcriticalSq]
    have hcriticalRatio :
        (2400 * P * theta) * (lcnt ^ 3 / (s ^ 2 * kr ^ 4)) < 1 := by
      calc
        _ ≤ (2400 * P * theta) * (1 / A ^ 2) :=
          mul_le_mul_of_nonneg_left hRatioCritical (by positivity)
        _ = 2400 * P * theta / A ^ 2 := by ring
        _ < 1 := hcriticalCoeff
    have hcriticalCross : 2400 * P * theta * lcnt ^ 3 < s ^ 2 * kr ^ 4 := by
      have hratio : (2400 * P * theta * lcnt ^ 3) / (s ^ 2 * kr ^ 4) < 1 := by
        convert hcriticalRatio using 1 <;> ring
      have h := (div_lt_iff₀ (by positivity : 0 < s ^ 2 * kr ^ 4)).mp hratio
      simpa using h
    have hDthree : 3 * (g.totalDegree : ℝ) ≤
        6 * P * theta * lcnt ^ 2 / (s * kr ^ 3) := by
      calc
        _ ≤ 3 * (2 * P * theta * lcnt ^ 2 / (s * kr ^ 3)) :=
          mul_le_mul_of_nonneg_left hDsmall (by positivity)
        _ = 6 * P * theta * lcnt ^ 2 / (s * kr ^ 3) := by ring
    have hDthreshold : 3 * (g.totalDegree : ℝ) < tau / 2 := by
      have hupper : 6 * P * theta * lcnt ^ 2 / (s * kr ^ 3) <
          s * kr / (400 * lcnt) := by
        apply (div_lt_div_iff₀ (mul_pos hspos (pow_pos hkpos 3))
          (mul_pos (by norm_num) hLpos)).2
        calc
          (6 * P * theta * lcnt ^ 2) * (400 * lcnt) =
              2400 * P * theta * lcnt ^ 3 := by ring
          _ < s ^ 2 * kr ^ 4 := hcriticalCross
          _ = (s * kr) * (s * kr ^ 3) := by ring
      have htauHalf : tau / 2 = s * kr / (400 * lcnt) := by dsimp [tau]; ring
      rw [htauHalf]
      exact hDthree.trans_lt hupper
    have h6DltTau : 6 * (g.totalDegree : ℝ) < tau := by
      nlinarith [hDthreshold, htauPos]
    have hOutcome (l : Line 3) (hl : l ∈ Lgood) :
        criticalLine g l ∨ flatLine g l := by
      let T := (pointsOn S l).filter (fun x => x ∈ Sstar)
      have hTcard : tau ≤ (T.card : ℝ) := by simpa [T] using hStarOnGood l hl
      have hTlargeReal : 6 * (g.totalDegree : ℝ) < (T.card : ℝ) :=
        h6DltTau.trans_le hTcard
      have hTlarge : 6 * g.totalDegree < T.card := by exact_mod_cast hTlargeReal
      have hTline : ∀ x ∈ T, x ∈ l.1 := by
        intro x hx
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      have hclass (x : E 3) (hx : x ∈ T) :
          criticalPoint g x ∨ flatPoint g x := by
        have hxstar : x ∈ Sstar := (Finset.mem_filter.mp hx).2
        rcases Finset.mem_filter.mp hxstar with ⟨_, ⟨_, hthree⟩⟩
        let Lx := Lz.filter (fun m => x ∈ m.1)
        have hLx : 3 ≤ Lx.card := by simpa [Lx, lineMultiplicity] using hthree
        obtain ⟨M, hMsub, hMcard⟩ := Finset.exists_subset_card_eq hLx
        obtain ⟨m₁, m₂, m₃, h12, h13, h23, hMeq⟩ := Finset.card_eq_three.mp hMcard
        have hm₁ : m₁ ∈ M := by rw [hMeq]; simp
        have hm₂ : m₂ ∈ M := by rw [hMeq]; simp
        have hm₃ : m₃ ∈ M := by rw [hMeq]; simp
        have hmem₁ : m₁ ∈ Lx := hMsub hm₁
        have hmem₂ : m₂ ∈ Lx := hMsub hm₂
        have hmem₃ : m₃ ∈ Lx := hMsub hm₃
        rcases Finset.mem_filter.mp hmem₁ with ⟨hm₁z, hx₁⟩
        rcases Finset.mem_filter.mp hmem₂ with ⟨hm₂z, hx₂⟩
        rcases Finset.mem_filter.mp hmem₃ with ⟨hm₃z, hx₃⟩
        have hpoly₁ : onPolynomial g m₁ := (Finset.mem_filter.mp hm₁z).2
        have hpoly₂ : onPolynomial g m₂ := (Finset.mem_filter.mp hm₂z).2
        have hpoly₃ : onPolynomial g m₃ := (Finset.mem_filter.mp hm₃z).2
        exact three_lines_critical_or_flat g x m₁ m₂ m₃ h12 h13 h23
          hpoly₁ hpoly₂ hpoly₃ hx₁ hx₂ hx₃
      let Tcrit := T.filter (fun x => criticalPoint g x)
      let Tflat := T.filter (fun x => flatPoint g x)
      have hcover : T ⊆ Tcrit ∪ Tflat := by
        intro x hx
        rcases hclass x hx with hc | hf
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hc⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hf⟩))
      have hTcardSplit : T.card ≤ Tcrit.card + Tflat.card := by
        calc
          T.card ≤ (Tcrit ∪ Tflat).card := Finset.card_le_card hcover
          _ ≤ Tcrit.card + Tflat.card := Finset.card_union_le _ _
      have hTcrit (x : E 3) (hx : x ∈ Tcrit) : criticalPoint g x :=
        (Finset.mem_filter.mp hx).2
      have hTflat (x : E 3) (hx : x ∈ Tflat) : flatPoint g x :=
        (Finset.mem_filter.mp hx).2
      have hmanyCrit := (many_critical_flat_points g l Tcrit
        (by intro x hx; exact hTline x (Finset.mem_filter.mp hx).1)).1
      have hmanyFlat := (many_critical_flat_points g l Tflat
        (by intro x hx; exact hTline x (Finset.mem_filter.mp hx).1)).2
      by_cases hcrit : g.totalDegree < Tcrit.card
      · exact Or.inl (hmanyCrit hcrit hTcrit)
      · have hcritLe : Tcrit.card ≤ g.totalDegree := Nat.le_of_not_lt hcrit
        have hflat : 3 * g.totalDegree < Tflat.card := by omega
        exact Or.inr (hmanyFlat hflat hTflat)
    let Lcritical := Lgood.filter (fun l => criticalLine g l)
    let Lflat := Lgood.filter (fun l => flatLine g l ∧ ¬ inPlaneComponent g l)
    let Lplane := Lgood.filter (fun l => inPlaneComponent g l)
    have hcoverGood : Lgood ⊆ Lcritical ∪ Lflat ∪ Lplane := by
      intro l hl
      rcases hOutcome l hl with hc | hf
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_filter.mpr ⟨hl, hc⟩
      · by_cases hp : inPlaneComponent g l
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_filter.mpr ⟨hl, hp⟩
        · apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_filter.mpr ⟨hl, hf, hp⟩
    have hcoverGoodCard : Lgood.card ≤ Lcritical.card + Lflat.card + Lplane.card := by
      calc
        Lgood.card ≤ (Lcritical ∪ Lflat ∪ Lplane).card := Finset.card_le_card hcoverGood
        _ ≤ (Lcritical ∪ Lflat).card + Lplane.card := Finset.card_union_le _ _
        _ ≤ Lcritical.card + Lflat.card + Lplane.card := by
          have h := Finset.card_union_le Lcritical Lflat
          omega
    obtain ⟨hcritFinite, hcritBound⟩ := critical_line_bound g hg hgsq
    have hcriticalCard : (Lcritical.card : ℝ) ≤
        (g.totalDegree : ℝ) * (g.totalDegree - 1 : ℕ) := by
      have hsub : (Lcritical : Set (Line 3)) ⊆ {l | criticalLine g l} := by
        intro l hl
        exact (Finset.mem_filter.mp hl).2
      have hN := Set.ncard_le_ncard hsub hcritFinite
      rw [Set.ncard_coe_finset] at hN
      have hcard : (Lcritical.card : ℝ) ≤
          ({l | criticalLine g l}.ncard : ℝ) := by exact_mod_cast hN
      exact hcard.trans hcritBound
    obtain ⟨hflatFinite, hflatBound⟩ := flat_line_bound g hg hgsq
    have hflatCard : (Lflat.card : ℝ) ≤ 3 * (g.totalDegree : ℝ) ^ 2 := by
      have hsub : (Lflat : Set (Line 3)) ⊆
          {l | flatLine g l ∧ ¬ inPlaneComponent g l} := by
        intro l hl
        exact (Finset.mem_filter.mp hl).2
      have hN := Set.ncard_le_ncard hsub hflatFinite
      rw [Set.ncard_coe_finset] at hN
      have hcard : (Lflat.card : ℝ) ≤
          ({l | flatLine g l ∧ ¬ inPlaneComponent g l}.ncard : ℝ) := by exact_mod_cast hN
      exact hcard.trans hflatBound
    have hDminus : ((g.totalDegree - 1 : ℕ) : ℝ) ≤ (g.totalDegree : ℝ) := by
      exact_mod_cast (Nat.sub_le (g.totalDegree) 1)
    have hcriticalSq : (Lcritical.card : ℝ) ≤ (g.totalDegree : ℝ) ^ 2 := by
      have hdegree := mul_le_mul_of_nonneg_left hDminus (by positivity : 0 ≤ (g.totalDegree : ℝ))
      calc
        (Lcritical.card : ℝ) ≤
            (g.totalDegree : ℝ) * (g.totalDegree - 1 : ℕ) := hcriticalCard
        _ ≤ (g.totalDegree : ℝ) ^ 2 := by simpa [pow_two] using hdegree
    have hkOne : 1 ≤ kr := by
      dsimp [kr]
      exact_mod_cast (show 1 ≤ k by omega)
    have hkrSq : kr ≤ kr ^ 2 := by
      calc
        kr = kr * 1 := (mul_one kr).symm
        _ ≤ kr * kr := mul_le_mul_of_nonneg_left hkOne (by positivity : 0 ≤ kr)
        _ = kr ^ 2 := by rw [pow_two]
    have hkSq : 1 ≤ kr ^ 2 := by
      calc
        1 ≤ kr := hkOne
        _ ≤ kr ^ 2 := hkrSq
    have hkPow : kr ^ 4 ≤ kr ^ 6 := by
      calc
        kr ^ 4 = kr ^ 4 * 1 := by ring
        _ ≤ kr ^ 4 * kr ^ 2 := mul_le_mul_of_nonneg_left hkSq (by positivity)
        _ = kr ^ 6 := by ring
    have hdenPow : s ^ 2 * kr ^ 4 ≤ s ^ 2 * kr ^ 6 :=
      mul_le_mul_of_nonneg_left hkPow (sq_nonneg s)
    have hRatioDegreeSmall : lcnt ^ 3 / (s ^ 2 * kr ^ 6) ≤ 1 / A ^ 2 := by
      calc
        lcnt ^ 3 / (s ^ 2 * kr ^ 6) ≤ lcnt ^ 3 / (s ^ 2 * kr ^ 4) := by
          apply (div_le_div_iff₀
            (mul_pos (sq_pos_of_pos hspos) (pow_pos hkpos 6))
            (mul_pos (sq_pos_of_pos hspos) (pow_pos hkpos 4))).2
          exact mul_le_mul_of_nonneg_left hdenPow (pow_nonneg hLpos.le 3)
        _ ≤ 1 / A ^ 2 := hRatioCritical
    have hDsq : (g.totalDegree : ℝ) ^ 2 ≤
        (2 * P * theta * lcnt ^ 2 / (s * kr ^ 3)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hDsmall 2
    have hDsqEq :
        (2 * P * theta * lcnt ^ 2 / (s * kr ^ 3)) ^ 2 =
          4 * P ^ 2 * theta ^ 2 * lcnt * (lcnt ^ 3 / (s ^ 2 * kr ^ 6)) := by
      field_simp [ne_of_gt hspos, ne_of_gt hkpos]
      <;> ring
    have hA80 : 80 * P * theta ≤ A := by
      have hAcritical' : 2400 * (P * theta) < A := by
        calc
          2400 * (P * theta) = 2400 * P * theta := by ring
          _ < A := hAcritical
      have hA80Strict : 80 * P * theta < A := by
        calc
          80 * P * theta = 80 * (P * theta) := by ring
          _ ≤ 2400 * (P * theta) :=
            mul_le_mul_of_nonneg_right (by norm_num) hPthetaPos.le
          _ < A := hAcritical'
      exact hA80Strict.le
    have hA80nonneg : 0 ≤ 80 * P * theta := by
      calc
        0 ≤ 80 * (P * theta) := mul_nonneg (by norm_num) hPthetaPos.le
        _ = 80 * P * theta := by ring
    have hA80sq : (80 * P * theta) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ hA80nonneg hA80 2
    have hdegreeCoeff : 4 * P ^ 2 * theta ^ 2 / A ^ 2 ≤ 1 / 1600 := by
      apply (div_le_iff₀ (sq_pos_of_pos hApos)).2
      calc
        4 * P ^ 2 * theta ^ 2 = (80 * P * theta) ^ 2 / 1600 := by ring
        _ ≤ A ^ 2 / 1600 :=
          div_le_div_of_nonneg_right hA80sq (by norm_num : 0 ≤ (1600 : ℝ))
        _ = (1 / 1600) * A ^ 2 := by ring
    have hDsqFinal : (g.totalDegree : ℝ) ^ 2 ≤ lcnt / 1600 := by
      calc
        (g.totalDegree : ℝ) ^ 2 ≤
            (2 * P * theta * lcnt ^ 2 / (s * kr ^ 3)) ^ 2 := hDsq
        _ = 4 * P ^ 2 * theta ^ 2 * lcnt * (lcnt ^ 3 / (s ^ 2 * kr ^ 6)) := hDsqEq
        _ ≤ 4 * P ^ 2 * theta ^ 2 * lcnt * (1 / A ^ 2) :=
          mul_le_mul_of_nonneg_left hRatioDegreeSmall (by positivity)
        _ = lcnt * (4 * P ^ 2 * theta ^ 2 / A ^ 2) := by ring
        _ ≤ lcnt * (1 / 1600) :=
          mul_le_mul_of_nonneg_left hdegreeCoeff hLpos.le
        _ = lcnt / 1600 := by ring
    have hExceptional : (Lcritical.card : ℝ) + (Lflat.card : ℝ) ≤ lcnt / 400 := by
      calc
        (Lcritical.card : ℝ) + (Lflat.card : ℝ) ≤
            (g.totalDegree : ℝ) ^ 2 + 3 * (g.totalDegree : ℝ) ^ 2 :=
          add_le_add hcriticalSq hflatCard
        _ = 4 * (g.totalDegree : ℝ) ^ 2 := by ring
        _ ≤ 4 * (lcnt / 1600) :=
          mul_le_mul_of_nonneg_left hDsqFinal (by norm_num)
        _ = lcnt / 400 := by ring
    have hgoodCardReal : (Lgood.card : ℝ) ≤
        (Lcritical.card : ℝ) + (Lflat.card : ℝ) + (Lplane.card : ℝ) := by
      exact_mod_cast hcoverGoodCard
    have hplaneLower : lcnt / 400 ≤ (Lplane.card : ℝ) := by
      linarith [hgoodBound, hgoodCardReal, hExceptional]
    let factorSet : Finset (Poly 3) :=
      (UniqueFactorizationMonoid.normalizedFactors g).toFinset
    let linearFactors : Finset (Poly 3) := factorSet.filter (fun q => q.totalDegree = 1)
    have hfactorCount : (linearFactors.card : ℝ) ≤ (g.totalDegree : ℝ) := by
      have hnat : linearFactors.card ≤ factorSet.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hnat' := hnat.trans (normalizedFactors_card_le_totalDegree g hg)
      exact_mod_cast hnat'
    let Hdefault : Plane 3 := Classical.choose
      (exists_plane_for_linear_polynomial (MvPolynomial.X (0 : Fin 3)) (by simp))
    let Hlinear : Poly 3 → Plane 3 := fun q =>
      if hq : q.totalDegree = 1 then Classical.choose (exists_plane_for_linear_polynomial q hq)
      else Hdefault
    have hHlinear (q : Poly 3) (hq : q ∈ linearFactors) (l : Line 3)
        (hl : onPolynomial q l) : l.1 ≤ (Hlinear q).1 := by
      have hqdegree := (Finset.mem_filter.mp hq).2
      simpa [Hlinear, hqdegree] using
        (Classical.choose_spec (exists_plane_for_linear_polynomial q hqdegree) l hl)
    let PlaneLines : Poly 3 → Finset (Line 3) := fun q =>
      Lplane.filter (fun l => l.1 ≤ (Hlinear q).1)
    have hLplaneSubset : Lplane ⊆ L := by
      exact Finset.Subset.trans (Finset.filter_subset _ _)
        (Finset.Subset.trans (Finset.filter_subset _ _)
          (Finset.filter_subset _ _))
    have hcapPlane (q : Poly 3) (hq : q ∈ linearFactors) :
        ((PlaneLines q).card : ℝ) ≤ B := by
      have hsub : PlaneLines q ⊆ L.filter (fun l => l.1 ≤ (Hlinear q).1) := by
        intro l hl
        rcases Finset.mem_filter.mp hl with ⟨hlplane, hcontained⟩
        exact Finset.mem_filter.mpr ⟨hLplaneSubset hlplane, hcontained⟩
      have hcard : ((PlaneLines q).card : ℝ) ≤
          ((L.filter (fun l => l.1 ≤ (Hlinear q).1)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub)
      exact hcard.trans (hplane (Hlinear q))
    let PlaneFactorLines : Finset (Line 3) := linearFactors.biUnion PlaneLines
    have hplaneFactorCover : Lplane ⊆ PlaneFactorLines := by
      intro l hl
      rcases Finset.mem_filter.mp hl with ⟨hlgood, hcomponent⟩
      rcases hcomponent with ⟨p, hpdegree, hpdvd, hpon⟩
      have hp0 : p ≠ 0 := by
        intro hpzero
        simp [hpzero] at hpdegree
      have hpirr := linearPolynomial_irreducible p hpdegree
      obtain ⟨q, hqmem, hAssoc⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hg hpirr hpdvd
      have hq0 : q ≠ 0 := by
        intro hqzero
        exact (UniqueFactorizationMonoid.zero_notMem_normalizedFactors g)
          (by simpa [hqzero] using hqmem)
      have hpdegLe : p.totalDegree ≤ q.totalDegree :=
        MvPolynomial.totalDegree_le_of_dvd_of_isDomain hAssoc.dvd hq0
      have hqdegLe : q.totalDegree ≤ p.totalDegree :=
        MvPolynomial.totalDegree_le_of_dvd_of_isDomain hAssoc.symm.dvd hp0
      have hqdegree : q.totalDegree = 1 := by
        have heq : q.totalDegree = p.totalDegree := Nat.le_antisymm hqdegLe hpdegLe
        rw [heq, hpdegree]
      have hqfactor : q ∈ linearFactors := by
        exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hqmem, hqdegree⟩
      have hqon : onPolynomial q l := by
        obtain ⟨t, ht⟩ := hAssoc.dvd
        intro x hx
        rw [ht]
        have hpx : MvPolynomial.eval x p = 0 := by
          simpa [evalR] using hpon x hx
        simp only [evalR, MvPolynomial.eval_mul]
        rw [hpx]
        simp
      have hcontained := hHlinear q hqfactor l hqon
      apply Finset.mem_biUnion.mpr
      refine ⟨q, hqfactor, ?_⟩
      exact Finset.mem_filter.mpr ⟨hl, hcontained⟩
    have hplaneFactorNat : Lplane.card ≤ PlaneFactorLines.card :=
      Finset.card_le_card hplaneFactorCover
    have hplaneFactorSum : PlaneFactorLines.card ≤
        ∑ q ∈ linearFactors, (PlaneLines q).card := by
      exact Finset.card_biUnion_le
    have hplaneFactorCount : (Lplane.card : ℝ) ≤
        (g.totalDegree : ℝ) * B := by
      have hcast : ((Lplane.card : ℕ) : ℝ) ≤
          ((∑ q ∈ linearFactors, (PlaneLines q).card : ℕ) : ℝ) := by
        exact_mod_cast hplaneFactorNat.trans hplaneFactorSum
      have hcast' : (Lplane.card : ℝ) ≤
          ∑ q ∈ linearFactors, ((PlaneLines q).card : ℝ) := by
        simpa only [Nat.cast_sum] using hcast
      have hsumCap : (∑ q ∈ linearFactors, ((PlaneLines q).card : ℝ)) ≤
          (linearFactors.card : ℝ) * B := by
        calc
          _ ≤ ∑ q ∈ linearFactors, B := by
            apply Finset.sum_le_sum
            intro q hq
            exact hcapPlane q hq
          _ = (linearFactors.card : ℝ) * B := by simp [mul_comm]
      exact hcast'.trans (hsumCap.trans (mul_le_mul_of_nonneg_right hfactorCount hB))
    have hplaneDegreeBound : (Lplane.card : ℝ) ≤
        2 * P * theta * lcnt ^ 2 * B / (s * kr ^ 3) := by
      calc
        (Lplane.card : ℝ) ≤ (g.totalDegree : ℝ) * B := hplaneFactorCount
        _ ≤ (2 * P * theta * lcnt ^ 2 / (s * kr ^ 3)) * B :=
          mul_le_mul_of_nonneg_right hDsmall hB
        _ = 2 * P * theta * lcnt ^ 2 * B / (s * kr ^ 3) := by ring
    have hplaneMiddle : lcnt / 400 ≤
        (2 * P * theta * lcnt ^ 2 * B) / (s * kr ^ 3) :=
      hplaneLower.trans hplaneDegreeBound
    have hplaneMul := (le_div_iff₀ (mul_pos hspos (pow_pos hkpos 3))).mp hplaneMiddle
    have hplaneCancelDiv : s * kr ^ 3 ≤
        (2 * P * theta * lcnt ^ 2 * B) / (lcnt / 400) := by
      apply (le_div_iff₀ (div_pos hLpos (by norm_num))).2
      calc
        (s * kr ^ 3) * (lcnt / 400) = (lcnt / 400) * (s * kr ^ 3) := by ring
        _ ≤ 2 * P * theta * lcnt ^ 2 * B := hplaneMul
    have hratioCancel :
        (2 * P * theta * lcnt ^ 2 * B) / (lcnt / 400) = 800 * P * theta * lcnt * B := by
      field_simp [ne_of_gt hLpos]
      <;> ring
    have hplaneProduct : s * kr ^ 3 ≤ 800 * P * theta * lcnt * B := by
      rw [hratioCancel] at hplaneCancelDiv
      exact hplaneCancelDiv
    have hmiddleBound : s ≤ 800 * P * theta * lcnt * B / kr ^ 3 :=
      (le_div_iff₀ (pow_pos hkpos 3)).2 hplaneProduct
    have hmiddleNonneg : 0 ≤ lcnt * B / kr ^ 3 := by positivity
    have hCoutBound : 800 * P * theta ≤ Cout := by
      dsimp [Cout]
      linarith
    have hlargeConclusion : s ≤ Cout * (lcnt * B / kr ^ 3) := by
      calc
        s ≤ 800 * P * theta * lcnt * B / kr ^ 3 := by
          simpa [mul_div_assoc, mul_assoc] using hmiddleBound
        _ = (800 * P * theta) * (lcnt * B / kr ^ 3) := by ring
        _ ≤ Cout * (lcnt * B / kr ^ 3) :=
          mul_le_mul_of_nonneg_right hCoutBound hmiddleNonneg
    have hCoutLe : Cout ≤ Cfinal := by dsimp [Cfinal]; linarith
    have hmidLe : lcnt * B / kr ^ 3 ≤ targetFinal := by
      have hother : 0 ≤ lcnt ^ ((3 : ℝ) / 2) / kr ^ 2 + lcnt / kr := by
        simpa [target] using htargetNonneg
      dsimp [targetFinal]
      linarith [hother]
    have hlargeFinal : s ≤ Cfinal * targetFinal := by
      calc
        s ≤ Cout * (lcnt * B / kr ^ 3) := hlargeConclusion
        _ ≤ Cfinal * (lcnt * B / kr ^ 3) :=
          mul_le_mul_of_nonneg_right hCoutLe hmiddleNonneg
        _ ≤ Cfinal * targetFinal :=
          mul_le_mul_of_nonneg_left hmidLe (by positivity)
    simpa [s, lcnt, kr, targetFinal] using hlargeFinal
/-- ci:rich-lines, CI:214–336; no quadric cap. -/
theorem ci_rich_lines : ∃ C : ℝ, 0 < C ∧
    ∀ (L : Finset (Line 3)) (B : ℝ) (k : ℕ),
      0 ≤ B → planeCap L B → 3 ≤ k →
      FiniteCardBound (richPoints L k) (C *
        ((L.card : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 +
          (L.card : ℝ) * B / (k : ℝ) ^ 3 + (L.card : ℝ) / k)) := by
  obtain ⟨C,hC,hUniform⟩ := rich_lines_uniform
  have hU := rich_line_uniformity_remove C hC (by simpa only [richLineBudget] using hUniform)
  refine ⟨2*C,by positivity,?_⟩
  intro L B k hB hcap hk
  simpa only [richLineBudget] using rich_line_tail_bound C hC L B hB
    (fun S j hj hS => hU L S B j hB hcap hj hS) k hk

end DistinctDistances.TrackC
