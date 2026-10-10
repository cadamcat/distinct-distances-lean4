import DistinctDistances.TrackE.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import DistinctDistances.TrackE.StarRankInputs

/-!
# Symmetric selections with independent stars (`reduction.tex:96-249`)

`red:directions` itself (direction caps on projective varieties) needs track A's variety model and
is stated in `TrackE/Directions.lean`. Its only consumer is the star-rank bound below, which is
elementary; so is everything downstream.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

set_option maxHeartbeats 1000000 in
/-- red:independent-stars.maximal (`reduction.tex:232-240`), abstract form. Let `G` be a
symmetric set of ordered pairs and attach a vector `vec p q` to each `(p,q) ∈ G`. If every set
`T` of partners of a vertex has rank at least `c₁ |T|`, then some symmetric `S ⊆ G` with at least
`c₁/(c₁+2) |G|` pairs has linearly independent vectors at every vertex. -/
theorem exists_independent_selection {α K V : Type*} [DecidableEq α] [Field K] [AddCommGroup V]
    [Module K V] (G : Finset (α × α)) (hG : ∀ e ∈ G, e.swap ∈ G) (vec : α → α → V)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hrank : ∀ p : α, ∀ T ⊆ (G.filter fun e => e.1 = p).image Prod.snd,
      c₁ * T.card ≤ Module.finrank K (Submodule.span K ((vec p) '' (T : Set α)))) :
    ∃ S ⊆ G, (∀ e ∈ S, e.swap ∈ S) ∧ c₁ / (c₁ + 2) * G.card ≤ S.card ∧
      ∀ p : α, LinearIndependent K
        (fun q : ((S.filter fun e => e.1 = p).image Prod.snd : Finset α) => vec p q) := by
  classical
  let partners (S : Finset (α × α)) (p : α) : Finset α :=
    (S.filter fun e => e.1 = p).image Prod.snd
  let Good : Finset (α × α) → Prop := fun S =>
    S ⊆ G ∧ (∀ e ∈ S, e.swap ∈ S) ∧
      ∀ p : α, LinearIndependent K
        (fun q : (partners S p : Finset α) => vec p q)
  let candidates := G.powerset.filter Good
  have hCandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simp), ?_⟩
    refine ⟨by simp, ?_, ?_⟩
    · simp
    · intro p
      rw [show partners (∅ : Finset (α × α)) p = ∅ by simp [partners]]
      exact linearIndependent_empty_type
  obtain ⟨S, hSCan, hSmax⟩ := Finset.exists_max_image candidates Finset.card hCandidates
  have hSgood : Good S := (Finset.mem_filter.mp hSCan).2
  have hSsub : S ⊆ G := hSgood.1
  have hSsymm : ∀ e ∈ S, e.swap ∈ S := hSgood.2.1
  have hSindep : ∀ p : α, LinearIndependent K
      (fun q : (partners S p : Finset α) => vec p q) := hSgood.2.2
  let vertices := G.image Prod.fst
  have hsourceCard (F : Finset (α × α)) (hFG : F ⊆ G) :
      F.card = ∑ p ∈ vertices, ((F.filter fun e => e.1 = p).image Prod.snd).card := by
    let fiber := fun p : α => F.filter fun e => e.1 = p
    have hUnion : vertices.biUnion fiber = F := by
      ext e
      constructor
      · intro he
        rcases Finset.mem_biUnion.mp he with ⟨p, hpV, hpF⟩
        exact (Finset.mem_filter.mp hpF).1
      · intro he
        have heG := hFG he
        apply Finset.mem_biUnion.mpr
        refine ⟨e.1, Finset.mem_image.mpr ⟨e, heG, rfl⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨he, rfl⟩
    have hDisjoint : (vertices : Set α).PairwiseDisjoint fiber := by
      intro p hpV q hqV hpq
      apply Finset.disjoint_left.mpr
      intro e hep heq
      have hep' := (Finset.mem_filter.mp hep).2
      have heq' := (Finset.mem_filter.mp heq).2
      exact hpq (hep'.symm.trans heq')
    have hFiberCard (p : α) :
        (fiber p).card = ((fiber p).image Prod.snd).card := by
      symm
      apply Finset.card_image_of_injOn
      intro e he e' he' hsnd
      have hefst := (Finset.mem_filter.mp he).2
      have he'fst := (Finset.mem_filter.mp he').2
      exact Prod.ext (hefst.trans he'fst.symm) hsnd
    calc
      F.card = (vertices.biUnion fiber).card := by rw [hUnion]
      _ = ∑ p ∈ vertices, (fiber p).card := Finset.card_biUnion hDisjoint
      _ = ∑ p ∈ vertices, ((fiber p).image Prod.snd).card := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hFiberCard p
  have hblock (e : α × α) (heG : e ∈ G) (heS : e ∉ S) :
      vec e.1 e.2 ∈ Submodule.span K (vec e.1 '' (partners S e.1 : Set α)) ∨
      vec e.2 e.1 ∈ Submodule.span K (vec e.2 '' (partners S e.2 : Set α)) := by
    rcases e with ⟨p, q⟩
    let e : α × α := (p, q)
    by_contra hn
    have hno1 : vec e.1 e.2 ∉ Submodule.span K (vec e.1 '' (partners S e.1 : Set α)) := by
      intro h
      exact hn (Or.inl h)
    have hno2 : vec e.2 e.1 ∉ Submodule.span K (vec e.2 '' (partners S e.2 : Set α)) := by
      intro h
      exact hn (Or.inr h)
    let S' := insert e (insert e.swap S)
    have hS'sub : S' ⊆ G := by
      intro f hf
      rcases Finset.mem_insert.mp hf with hfe | hf
      · rw [hfe]
        exact heG
      · rcases Finset.mem_insert.mp hf with hfswap | hf
        · rw [hfswap]
          exact hG e heG
        · exact hSsub hf
    have hS'symm : ∀ f ∈ S', f.swap ∈ S' := by
      intro f hf
      rcases Finset.mem_insert.mp hf with hfe | hf
      · rw [hfe]
        simp [S', e]
      · rcases Finset.mem_insert.mp hf with hfswap | hf
        · rw [hfswap]
          simp [S', e]
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hSsymm f hf))
    have hstar1 : partners S' e.1 = insert e.2 (partners S e.1) := by
      ext q
      simp [S', partners, e] <;> aesop
    have hstar2 : partners S' e.2 = insert e.1 (partners S e.2) := by
      ext q
      simp [S', partners, e] <;> aesop
    have hstarOther (p : α) (hp1 : p ≠ e.1) (hp2 : p ≠ e.2) :
        partners S' p = partners S p := by
      ext q
      simp [S', partners, e, hp1, hp2, ne_comm] <;> aesop
    have hqnot : e.2 ∉ partners S e.1 := by
      intro hq
      apply hno1
      exact Submodule.subset_span ⟨e.2, hq, rfl⟩
    have hpnot : e.1 ∉ partners S e.2 := by
      intro hp
      apply hno2
      exact Submodule.subset_span ⟨e.1, hp, rfl⟩
    have hNew1 : LinearIndependent K
        (fun x : Option (partners S e.1) => Option.casesOn' x (vec e.1 e.2) (fun y => vec e.1 y)) := by
      have hrange : Set.range (fun y : partners S e.1 => vec e.1 y) =
          vec e.1 '' (partners S e.1 : Set α) := by
        ext v
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨y, y.2, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
      have hnoRange : vec e.1 e.2 ∉
          Submodule.span K (Set.range (fun y : partners S e.1 => vec e.1 y)) := by
        simpa [hrange] using hno1
      exact LinearIndependent.option (hSindep e.1) hnoRange
    have hNew2 : LinearIndependent K
        (fun x : Option (partners S e.2) => Option.casesOn' x (vec e.2 e.1) (fun y => vec e.2 y)) := by
      have hrange : Set.range (fun y : partners S e.2 => vec e.2 y) =
          vec e.2 '' (partners S e.2 : Set α) := by
        ext v
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨y, y.2, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
      have hnoRange : vec e.2 e.1 ∉
          Submodule.span K (Set.range (fun y : partners S e.2 => vec e.2 y)) := by
        simpa [hrange] using hno2
      exact LinearIndependent.option (hSindep e.2) hnoRange
    let eSub1 := Finset.subtypeInsertEquivOption hqnot
    have hfun1 : (fun x : Option (partners S e.1) =>
        Option.casesOn' x (vec e.1 e.2) (fun y => vec e.1 y)) ∘ eSub1 =
          fun x : (insert e.2 (partners S e.1) : Finset α) => vec e.1 x := by
      funext x
      by_cases hx : (x : α) = e.2
      · have hx' : x = ⟨e.2, Finset.mem_insert_self _ _⟩ := Subtype.ext hx
        subst x
        simp [eSub1, Finset.subtypeInsertEquivOption]
      · simp [eSub1, Finset.subtypeInsertEquivOption, hx]
    let eSub2 := Finset.subtypeInsertEquivOption hpnot
    have hfun2 : (fun x : Option (partners S e.2) =>
        Option.casesOn' x (vec e.2 e.1) (fun y => vec e.2 y)) ∘ eSub2 =
          fun x : (insert e.1 (partners S e.2) : Finset α) => vec e.2 x := by
      funext x
      by_cases hx : (x : α) = e.1
      · have hx' : x = ⟨e.1, Finset.mem_insert_self _ _⟩ := Subtype.ext hx
        subst x
        simp [eSub2, Finset.subtypeInsertEquivOption]
      · simp [eSub2, Finset.subtypeInsertEquivOption, hx]
    have hNew1Fin : LinearIndependent K
        (fun x : (insert e.2 (partners S e.1) : Finset α) => vec e.1 x) :=
      (linearIndependent_equiv' eSub1 hfun1).mpr hNew1
    have hNew2Fin : LinearIndependent K
        (fun x : (insert e.1 (partners S e.2) : Finset α) => vec e.2 x) :=
      (linearIndependent_equiv' eSub2 hfun2).mpr hNew2
    have hS'Indep : ∀ p : α, LinearIndependent K
        (fun q : (partners S' p : Finset α) => vec p q) := by
      intro p
      by_cases hp1 : p = e.1
      · subst p
        rw [hstar1]
        exact hNew1Fin
      · by_cases hp2 : p = e.2
        · subst p
          rw [hstar2]
          exact hNew2Fin
        · rw [hstarOther p hp1 hp2]
          exact hSindep p
    have hS'good : Good S' := ⟨hS'sub, hS'symm, hS'Indep⟩
    have hS'can : S' ∈ candidates := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hS'sub, hS'good⟩
    have hS'le : S'.card ≤ S.card := hSmax S' hS'can
    have hSsubset' : S ⊆ S' := by
      intro f hf
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hf)
    have hS'neq : S ≠ S' := by
      intro hEq
      apply heS
      have heIn : e ∈ S' := by simp [S', e]
      simpa [hEq] using heIn
    have hS'card : S.card < S'.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSsubset', hS'neq⟩)
    omega
  let bad := (G \ S).filter fun e =>
    vec e.1 e.2 ∈ Submodule.span K (vec e.1 '' (partners S e.1 : Set α))
  have hBadSub : bad ⊆ G := by
    intro e he
    exact (Finset.mem_sdiff.mp ((Finset.mem_filter.mp he).1)).1
  have hBadCover : G \ S ⊆ bad ∪ bad.image Prod.swap := by
    intro e he
    have heG := (Finset.mem_sdiff.mp he).1
    have heS : e ∉ S := (Finset.mem_sdiff.mp he).2
    rcases hblock e heG heS with hleft | hright
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hleft⟩))
    · have hswapG : e.swap ∈ G := hG e heG
      have hswapS : e.swap ∉ S := by
        intro hs
        apply heS
        simpa using hSsymm e.swap hs
      have hswapBad : e.swap ∈ bad := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_sdiff.mpr ⟨hswapG, hswapS⟩, ?_⟩
        simpa using hright
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e.swap, hswapBad, by simp⟩))
  have hBadCard : (G \ S).card ≤ 2 * bad.card := by
    calc
      (G \ S).card ≤ (bad ∪ bad.image Prod.swap).card := Finset.card_le_card hBadCover
      _ ≤ bad.card + (bad.image Prod.swap).card := Finset.card_union_le _ _
      _ = 2 * bad.card := by
        have hswapCard : (bad.image Prod.swap).card = bad.card := by
          apply Finset.card_image_of_injOn
          intro e he e' he' hs
          exact Prod.ext (congrArg Prod.fst (congrArg Prod.swap hs))
            (congrArg Prod.snd (congrArg Prod.swap hs))
        rw [hswapCard]
        omega
  have hBadSum := hsourceCard bad hBadSub
  have hStarSum := hsourceCard S hSsub
  have hBadSumR : (bad.card : ℝ) =
      ∑ p ∈ vertices, (((bad.filter fun e => e.1 = p).image Prod.snd).card : ℝ) := by
    exact_mod_cast hBadSum
  have hStarSumR : (∑ p ∈ vertices, (partners S p).card : ℝ) = (S.card : ℝ) := by
    have h := hStarSum
    simpa [partners] using congrArg (fun n : ℕ => (n : ℝ)) h.symm
  have hBadBound (p : α) (hpV : p ∈ vertices) :
      c₁ * (((bad.filter fun e => e.1 = p).image Prod.snd).card : ℝ) ≤
        ((partners S p).card : ℝ) := by
    let T := (bad.filter fun e => e.1 = p).image Prod.snd
    have hTsub : T ⊆ (G.filter fun e => e.1 = p).image Prod.snd := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
      have heB := (Finset.mem_filter.mp he).1
      have heG := (Finset.mem_sdiff.mp ((Finset.mem_filter.mp heB).1)).1
      have hep := (Finset.mem_filter.mp he).2
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heG, hep⟩, rfl⟩
    have hvec : ∀ q ∈ T, vec p q ∈ Submodule.span K (vec p '' (partners S p : Set α)) := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
      have heB := (Finset.mem_filter.mp he).1
      have hefirst := (Finset.mem_filter.mp he).2
      have hcond := (Finset.mem_filter.mp heB).2
      simpa [hefirst] using hcond
    have hspan : Submodule.span K (vec p '' (T : Set α)) ≤
        Submodule.span K (vec p '' (partners S p : Set α)) := by
      apply Submodule.span_le.2
      rintro _ ⟨q, hq, rfl⟩
      exact hvec q hq
    letI : FiniteDimensional K (Submodule.span K (vec p '' (partners S p : Set α))) :=
      FiniteDimensional.span_of_finite K
        (Set.Finite.image (vec p) (Set.toFinite (partners S p : Set α)))
    have hdim : Module.finrank K (Submodule.span K (vec p '' (T : Set α))) ≤
        Module.finrank K (Submodule.span K (vec p '' (partners S p : Set α))) :=
      Submodule.finrank_mono hspan
    have hdimS : Module.finrank K (Submodule.span K (vec p '' (partners S p : Set α))) ≤
        (partners S p).card := by
      have himage : ((partners S p).image (vec p) : Set V) =
          vec p '' (partners S p : Set α) := by
        ext x
        simp
      rw [← himage]
      calc
        Module.finrank K (Submodule.span K
            (((partners S p).image (vec p) : Finset V) : Set V)) ≤
            ((partners S p).image (vec p)).card := by
              simpa only [Set.finrank] using finrank_span_finset_le_card ((partners S p).image (vec p))
        _ ≤ (partners S p).card := Finset.card_image_le
    have hr := hrank p T hTsub
    have hdimR : (Module.finrank K (Submodule.span K (vec p '' (T : Set α))) : ℝ) ≤
        (Module.finrank K (Submodule.span K (vec p '' (partners S p : Set α))) : ℝ) := by
      exact_mod_cast hdim
    have hdimSR : (Module.finrank K (Submodule.span K (vec p '' (partners S p : Set α))) : ℝ) ≤
        (partners S p).card := by
      exact_mod_cast hdimS
    have hrR : c₁ * (T.card : ℝ) ≤
        (Module.finrank K (Submodule.span K (vec p '' (T : Set α))) : ℝ) := hr
    exact hrR.trans (hdimR.trans hdimSR)
  have hsumBound : c₁ * (bad.card : ℝ) ≤ (S.card : ℝ) := by
    calc
      c₁ * (bad.card : ℝ) =
          ∑ p ∈ vertices, c₁ * (((bad.filter fun e => e.1 = p).image Prod.snd).card : ℝ) := by
            rw [hBadSumR, Finset.mul_sum]
      _ ≤ ∑ p ∈ vertices, ((partners S p).card : ℝ) :=
        Finset.sum_le_sum fun p hp => hBadBound p hp
      _ = (S.card : ℝ) := hStarSumR
  have hBadCardR : ((G \ S).card : ℝ) ≤ 2 * (bad.card : ℝ) := by exact_mod_cast hBadCard
  have hdelScaled : c₁ * ((G \ S).card : ℝ) ≤ 2 * (S.card : ℝ) := by
    calc
      c₁ * ((G \ S).card : ℝ) ≤ c₁ * (2 * (bad.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hBadCardR (le_of_lt hc₁)
      _ = 2 * (c₁ * (bad.card : ℝ)) := by ring
      _ ≤ 2 * (S.card : ℝ) := mul_le_mul_of_nonneg_left hsumBound (by norm_num)
  have hPartition : (G \ S).card + S.card = G.card := Finset.card_sdiff_add_card_eq_card hSsub
  have hPartitionR : ((G \ S).card : ℝ) + (S.card : ℝ) = (G.card : ℝ) := by exact_mod_cast hPartition
  have hTotal : c₁ * (G.card : ℝ) ≤ (c₁ + 2) * (S.card : ℝ) := by
    rw [← hPartitionR]
    nlinarith [hdelScaled]
  have hden : 0 < c₁ + 2 := by linarith
  refine ⟨S, hSsub, hSsymm, ?_, ?_⟩
  · have hratio : (c₁ * (G.card : ℝ)) / (c₁ + 2) ≤ (S.card : ℝ) :=
      (div_le_iff₀ hden).2 (by simpa [mul_comm] using hTotal)
    simpa [div_mul_eq_mul_div] using hratio
  · simpa [partners] using hSindep

variable {d : ℕ}

/-- Homogeneous monomial scaling for `aeval`: evaluating at `c • v` scales by `c ^ D`
when the exponent has degree `D`. -/
theorem independentStar_aeval_monomial_smul {D : ℕ} (c : ℂ) (v : Fin d → ℂ)
    (s : Fin d →₀ ℕ) (a : ℂ) (hs : s.degree = D) :
    MvPolynomial.aeval (c • v) (MvPolynomial.monomial s a) =
      c ^ D * MvPolynomial.aeval v (MvPolynomial.monomial s a) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hsmul : ∀ i : Fin d, ((c • v) i) = c * v i := fun i => by
    simp [Pi.smul_apply, smul_eq_mul]
  have hprod : s.prod (fun i k => ((c • v) i) ^ k) =
      c ^ D * s.prod (fun i k => (v i) ^ k) := by
    simp only [Finsupp.prod]
    calc ∏ i ∈ s.support, (((c • v) i) ^ (s i))
        = ∏ i ∈ s.support, (c ^ (s i) * (v i) ^ (s i)) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [hsmul i, mul_pow]
      _ = (∏ i ∈ s.support, c ^ (s i)) * (∏ i ∈ s.support, (v i) ^ (s i)) :=
        Finset.prod_mul_distrib
      _ = c ^ D * (∏ i ∈ s.support, (v i) ^ (s i)) := by
        congr 1
        rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hs]
  calc a * s.prod (fun i k => ((c • v) i) ^ k)
      = a * (c ^ D * s.prod (fun i k => (v i) ^ k)) := by rw [hprod]
    _ = c ^ D * (a * s.prod (fun i k => (v i) ^ k)) := by ring

/-- Homogeneous scaling for `aeval`: evaluating a homogeneous degree-`D` polynomial at
`c • v` scales by `c ^ D`. -/
theorem independentStar_aeval_homogeneous_smul {D : ℕ} (c : ℂ) (v : Fin d → ℂ)
    (p : MvPolynomial (Fin d) ℂ) (h : p.IsHomogeneous D) :
    MvPolynomial.aeval (c • v) p = c ^ D * MvPolynomial.aeval v p := by
  have hexpand : ∀ w : Fin d → ℂ, MvPolynomial.aeval w p =
      ∑ s ∈ p.support, MvPolynomial.aeval w (MvPolynomial.monomial s (p.coeff s)) := by
    intro w
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
  rw [hexpand (c • v), hexpand v, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsum : D = ∑ i ∈ s.support, s i := h.degree_eq_sum_deg_support hs
  have hdeg : s.degree = D := by
    rw [Finsupp.degree_apply]
    exact hsum.symm
  exact independentStar_aeval_monomial_smul c v s (p.coeff s) hdeg

/-- Homogeneous scaling for `homEval`: the degree-`D` evaluation functional at `c • v`
is `c ^ D` times the one at `v`. -/
theorem independentStar_homEval_smul {D : ℕ} (c : ℂ) (v : Fin d → ℂ) :
    homEval d D (c • v) = c ^ D • homEval d D v := by
  ext ⟨p, hp⟩
  show MvPolynomial.aeval (c • v) p = (c ^ D • homEval d D v) ⟨p, hp⟩
  rw [LinearMap.smul_apply]
  show MvPolynomial.aeval (c • v) p = c ^ D • MvPolynomial.aeval v p
  rw [smul_eq_mul]
  exact independentStar_aeval_homogeneous_smul c v p
    ((MvPolynomial.mem_homogeneousSubmodule D p).mp hp)

/-- Complexification commutes with real scaling. -/
theorem independentStar_cplx_smul (t : ℝ) (a : RPoint d) :
    cplx (t • a) = (t : ℂ) • cplx a := by
  ext i
  simp [cplx]

/-- red:u-unique-direction (`reduction.tex:247-249`): an independent star has at most one
partner in each real projective direction. -/
theorem _root_.DistinctDistances.IndependentStar.eq_of_smul {D : ℕ} {p : RPoint d} {T : Finset (RPoint d)}
    (hT : IndependentStar D p T) {q q' : RPoint d} (hq : q ∈ T) (hq' : q' ∈ T) (t : ℝ)
    (h : q' - p = t • (q - p)) : q' = q := by
  have hcmplx : cplx (q' - p) = (t : ℂ) • cplx (q - p) := by
    rw [h]
    exact independentStar_cplx_smul t (q - p)
  have hscale : homEval d D (cplx (q' - p)) =
      ((t : ℂ) ^ D) • homEval d D (cplx (q - p)) := by
    rw [hcmplx]
    exact independentStar_homEval_smul ((t : ℂ)) (cplx (q - p))
  have hidx : (⟨q', hq'⟩ : T) = ⟨q, hq⟩ :=
    hT.eq_of_smul_apply_eq_smul_apply (1 : ℂ) (((t : ℂ) ^ D))
      ⟨q', hq'⟩ ⟨q, hq⟩ one_ne_zero (by simpa using hscale)
  exact congrArg Subtype.val hidx

open Classical in
/-- Independence of a star is preserved by a linear isometry (transport of the selection to the
rotated copy `Q = RP`, `reduction.tex:253-254`). -/
theorem _root_.DistinctDistances.IndependentStar.image_linearIsometryEquiv {D : ℕ} {p : RPoint d} {T : Finset (RPoint d)}
    (hT : IndependentStar D p T) (R : RPoint d ≃ₗᵢ[ℝ] RPoint d) :
    IndependentStar D (R p) (T.image R) := by
  classical
  let H := MvPolynomial.homogeneousSubmodule (Fin d) ℂ D
  let sub (L : RPoint d ≃ₗ[ℝ] RPoint d) (i : Fin d) : MvPolynomial (Fin d) ℂ :=
    ∑ j : Fin d, MvPolynomial.C
      (((L (EuclideanSpace.basisFun (Fin d) ℝ j)) i : ℝ) : ℂ) * MvPolynomial.X j
  have hsubHom (L : RPoint d ≃ₗ[ℝ] RPoint d) (i : Fin d) : (sub L i).IsHomogeneous 1 := by
    change (∑ j : Fin d,
      MvPolynomial.C (((L (EuclideanSpace.basisFun (Fin d) ℝ j)) i : ℝ) : ℂ) *
        MvPolynomial.X j).IsHomogeneous 1
    apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  have hrepr (v : RPoint d) :
      v = ∑ j : Fin d, v j • EuclideanSpace.basisFun (Fin d) ℝ j := by
    simpa [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v |>.symm
  have hcoeff (A B : RPoint d ≃ₗ[ℝ] RPoint d) (hAB : ∀ x, A (B x) = x)
      (i k : Fin d) :
      ∑ j : Fin d, (A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
          (B (EuclideanSpace.basisFun (Fin d) ℝ k) j) =
        (EuclideanSpace.basisFun (Fin d) ℝ k) i := by
    have hreprB : B (EuclideanSpace.basisFun (Fin d) ℝ k) =
        ∑ j : Fin d, B (EuclideanSpace.basisFun (Fin d) ℝ k) j •
          EuclideanSpace.basisFun (Fin d) ℝ j := hrepr _
    have h := congrArg (fun x : RPoint d => x i) (congrArg A hreprB)
    rw [hAB] at h
    simpa [map_sum, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm
  have hsubComp (A B : RPoint d ≃ₗ[ℝ] RPoint d) (hAB : ∀ x, A (B x) = x) :
      (MvPolynomial.aeval (sub B)).comp (MvPolynomial.aeval (sub A)) =
        AlgHom.id ℂ (MvPolynomial (Fin d) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X]
    change MvPolynomial.aeval (sub B) (sub A i) = MvPolynomial.X i
    calc
      MvPolynomial.aeval (sub B) (sub A i) =
          ∑ j : Fin d, MvPolynomial.C
            (algebraMap ℝ ℂ (A (EuclideanSpace.basisFun (Fin d) ℝ j) i)) *
            (∑ k : Fin d, MvPolynomial.C
              (algebraMap ℝ ℂ (B (EuclideanSpace.basisFun (Fin d) ℝ k) j)) *
              MvPolynomial.X k) := by
        simp [sub]
      _ = ∑ k : Fin d, (∑ j : Fin d,
            MvPolynomial.C (algebraMap ℝ ℂ (A (EuclideanSpace.basisFun (Fin d) ℝ j) i)) *
              MvPolynomial.C (algebraMap ℝ ℂ (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))) *
              MvPolynomial.X k := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        have hsum := Finset.sum_mul (Finset.univ : Finset (Fin d))
          (fun j : Fin d =>
            MvPolynomial.C (algebraMap ℝ ℂ (A (EuclideanSpace.basisFun (Fin d) ℝ j) i)) *
              MvPolynomial.C (algebraMap ℝ ℂ (B (EuclideanSpace.basisFun (Fin d) ℝ k) j)))
          (MvPolynomial.X k)
        simpa [mul_assoc] using hsum.symm
      _ = ∑ k : Fin d,
          MvPolynomial.C (algebraMap ℝ ℂ ((EuclideanSpace.basisFun (Fin d) ℝ k) i)) *
            MvPolynomial.X k := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        have hCsum : (∑ j : Fin d,
            MvPolynomial.C (σ := Fin d) (algebraMap ℝ ℂ
              ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
                (B (EuclideanSpace.basisFun (Fin d) ℝ k) j)))) =
            MvPolynomial.C (σ := Fin d) (∑ j : Fin d, algebraMap ℝ ℂ
              ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
                (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))) := by
          simpa using (map_sum (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ)
            (fun j : Fin d => algebraMap ℝ ℂ
              ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
                (B (EuclideanSpace.basisFun (Fin d) ℝ k) j)))
            (Finset.univ : Finset (Fin d))).symm
        have hMap : (∑ j : Fin d, algebraMap ℝ ℂ
            ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
              (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))) =
            algebraMap ℝ ℂ (∑ j : Fin d,
              (A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
                (B (EuclideanSpace.basisFun (Fin d) ℝ k) j)) := by
          simpa using (map_sum (algebraMap ℝ ℂ)
            (fun j : Fin d => (A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
              (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))
            (Finset.univ : Finset (Fin d))).symm
        calc
          (∑ j : Fin d,
              MvPolynomial.C (σ := Fin d) (algebraMap ℝ ℂ (A (EuclideanSpace.basisFun (Fin d) ℝ j) i)) *
                MvPolynomial.C (σ := Fin d) (algebraMap ℝ ℂ (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))) =
              ∑ j : Fin d, MvPolynomial.C (σ := Fin d) (algebraMap ℝ ℂ
                ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
                  (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [map_mul]
          _ = MvPolynomial.C (σ := Fin d) (∑ j : Fin d, algebraMap ℝ ℂ
              ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
                (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))) := hCsum
          _ = MvPolynomial.C (σ := Fin d) (algebraMap ℝ ℂ (∑ j : Fin d,
              (A (EuclideanSpace.basisFun (Fin d) ℝ j) i) *
                (B (EuclideanSpace.basisFun (Fin d) ℝ k) j))) :=
            congrArg (fun x : ℂ => MvPolynomial.C (σ := Fin d) x) hMap
          _ = MvPolynomial.C (σ := Fin d) (algebraMap ℝ ℂ
              ((EuclideanSpace.basisFun (Fin d) ℝ k) i)) := by
            exact congrArg (fun x : ℂ => MvPolynomial.C (σ := Fin d) x)
              (congrArg (algebraMap ℝ ℂ) (hcoeff A B hAB i k))
      _ = MvPolynomial.X i := by simp
  have hsubEval (L : RPoint d ≃ₗ[ℝ] RPoint d) (v : RPoint d) (i : Fin d) :
      MvPolynomial.aeval (cplx v) (sub L i) = cplx (L v) i := by
    have hreprL : L v = ∑ j : Fin d,
        v j • L (EuclideanSpace.basisFun (Fin d) ℝ j) := by
      calc
        L v = L (∑ j : Fin d, v j • EuclideanSpace.basisFun (Fin d) ℝ j) :=
          congrArg L (hrepr v)
        _ = ∑ j : Fin d, v j • L (EuclideanSpace.basisFun (Fin d) ℝ j) := by simp
    have hreal : ∑ j : Fin d,
        (L (EuclideanSpace.basisFun (Fin d) ℝ j) i) * v j = (L v) i := by
      have h := congrArg (fun x : RPoint d => x i) hreprL
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm
    change MvPolynomial.aeval (fun j => algebraMap ℝ ℂ (v j)) (sub L i) =
      algebraMap ℝ ℂ ((L v) i)
    calc
      MvPolynomial.aeval (fun j => algebraMap ℝ ℂ (v j)) (sub L i) =
          algebraMap ℝ ℂ (∑ j : Fin d,
            (L (EuclideanSpace.basisFun (Fin d) ℝ j) i) * v j) := by
        simp [sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_C,
          MvPolynomial.eval₂_X, map_sum, map_mul]
      _ = algebraMap ℝ ℂ ((L v) i) := congrArg (algebraMap ℝ ℂ) hreal
  let pull (L : RPoint d ≃ₗ[ℝ] RPoint d) : H →ₗ[ℂ] H :=
    { toFun := fun f => ⟨MvPolynomial.aeval (sub L) (f : MvPolynomial (Fin d) ℂ), by
        have hf : (f : MvPolynomial (Fin d) ℂ).IsHomogeneous D := f.2
        have h := hf.aeval (sub L) (hsubHom L)
        simpa [H] using h
      ⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        exact map_add (MvPolynomial.aeval (sub L)) (f : MvPolynomial (Fin d) ℂ)
          (g : MvPolynomial (Fin d) ℂ)
      map_smul' := by
        intro c f
        apply Subtype.ext
        exact map_smul (MvPolynomial.aeval (sub L)) c (f : MvPolynomial (Fin d) ℂ) }
  let L := R.toLinearEquiv
  have hpullLeft : (pull L.symm).comp (pull L) = LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.aeval (sub L.symm)
      (MvPolynomial.aeval (sub L) (f : MvPolynomial (Fin d) ℂ)) = (f : MvPolynomial (Fin d) ℂ)
    rw [← AlgHom.comp_apply, hsubComp L L.symm (fun x => L.apply_symm_apply x)]
    rfl
  have hpullRight : (pull L).comp (pull L.symm) = LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.aeval (sub L)
      (MvPolynomial.aeval (sub L.symm) (f : MvPolynomial (Fin d) ℂ)) = (f : MvPolynomial (Fin d) ℂ)
    rw [← AlgHom.comp_apply, hsubComp L.symm L (fun x => L.symm_apply_apply x)]
    rfl
  let pullEquiv : H ≃ₗ[ℂ] H :=
    LinearEquiv.ofLinearMap (pull L) (pull L.symm) hpullRight hpullLeft
  have hEval (v : RPoint d) :
      homEval d D (cplx (R v)) = pullEquiv.dualMap (homEval d D (cplx v)) := by
    ext f
    change MvPolynomial.aeval (cplx (R v)) (f : MvPolynomial (Fin d) ℂ) =
      MvPolynomial.aeval (cplx v) (MvPolynomial.aeval (sub L) (f : MvPolynomial (Fin d) ℂ))
    calc
      MvPolynomial.aeval (cplx (R v)) (f : MvPolynomial (Fin d) ℂ) =
          MvPolynomial.aeval (fun i => MvPolynomial.aeval (cplx v) (sub L i))
            (f : MvPolynomial (Fin d) ℂ) := by
        have hvec : (fun i => MvPolynomial.aeval (cplx v) (sub L i)) = cplx (R v) := by
          funext i
          simpa [L] using hsubEval L v i
        exact (congrArg (fun w => MvPolynomial.aeval w (f : MvPolynomial (Fin d) ℂ)) hvec).symm
      _ = MvPolynomial.aeval (cplx v)
          (MvPolynomial.aeval (sub L) (f : MvPolynomial (Fin d) ℂ)) := by
        rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
  let eT : T ≃ (T.image R) :=
    { toFun := fun q => ⟨R q, Finset.mem_image.mpr ⟨q, q.2, rfl⟩⟩
      invFun := fun q => ⟨R.symm q, by
        rcases Finset.mem_image.mp q.2 with ⟨x, hx, hq⟩
        have heq : R.symm (q : RPoint d) = x := by rw [← hq]; simp
        simpa [heq] using hx
      ⟩
      left_inv := by intro q; apply Subtype.ext; exact R.symm_apply_apply q
      right_inv := by intro q; apply Subtype.ext; exact R.apply_symm_apply q }
  have hfamily :
      (fun q : T.image R => homEval d D (cplx ((q : RPoint d) - R p))) ∘ eT =
        (fun q : T => pullEquiv.dualMap (homEval d D (cplx ((q : RPoint d) - p)))) := by
    funext q
    apply LinearMap.ext
    intro f
    simp only [Function.comp_apply]
    have hdiff : (R (q : RPoint d) - R p) = R ((q : RPoint d) - p) :=
      (map_sub R.toLinearMap (q : RPoint d) p).symm
    rw [show ((eT q : RPoint d) - R p) = R ((q : RPoint d) - p) by simpa [eT] using hdiff]
    simpa [L] using congrArg (fun g : Module.Dual ℂ H => g f) (hEval ((q : RPoint d) - p))
  change LinearIndependent ℂ
    (fun q : T.image R => homEval d D (cplx ((q : RPoint d) - R p)))
  change LinearIndependent ℂ
    (fun q : T => homEval d D (cplx ((q : RPoint d) - p))) at hT
  have hmapped : LinearIndependent ℂ
      (fun q : T => pullEquiv.dualMap (homEval d D (cplx ((q : RPoint d) - p)))) := by
    change LinearIndependent ℂ
      ((pullEquiv.dualMap).toLinearMap ∘ fun q : T => homEval d D (cplx ((q : RPoint d) - p)))
    exact hT.map' (pullEquiv.dualMap).toLinearMap
      (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective (pullEquiv.dualMap)))
  exact (linearIndependent_equiv' eT hfamily).mp hmapped

set_option maxHeartbeats 1000000 in
/-- red:independent-stars.rank (`reduction.tex:214-230`, from `red:directions` and
`poly:hilbert`): a positive-density symmetric selection `G` on which every set `T` of partners
of a vertex has homogeneous degree-`⌊A⌋` rank at least `c₁ |T|`. -/
theorem exists_selection_starRank (hd : 3 ≤ d) (hIH : IH d) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ,
      ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ ε₀ * Ascale d P.card →
        ∃ G : Finset (RPoint d × RPoint d), IsSymmSelection P G ∧
          c₀ * (P.card : ℝ) ^ 2 ≤ G.card ∧
          ∀ p : RPoint d, ∀ T ⊆ star G p,
            c₁ * T.card ≤ starRank (testDegree d P.card) p T := by
  classical
  obtain ⟨c₀, C, hc₀, hC, ε₀, hε₀, N₀, hselect⟩ := exists_selection_directionCaps hd hIH
  obtain ⟨c, hc, henv⟩ := TrackA.poly_envelope_projective_lower d
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hden : 0 < C * (2 : ℝ) ^ d := by positivity
  let c₁ : ℝ := (c : ℝ) / (C * (2 : ℝ) ^ d)
  refine ⟨c₀, c₁, hc₀, div_pos hcR hden, ε₀, hε₀, max N₀ 2, ?_⟩
  intro P hN hMP
  obtain ⟨G, hG, hGcard, hcap⟩ := hselect P ((Nat.le_max_left _ _).trans hN) hMP
  refine ⟨G, hG, hGcard, ?_⟩
  intro p T hT
  have hP : 2 ≤ P.card := (Nat.le_max_right _ _).trans hN
  let A := Ascale d P.card
  let D := testDegree d P.card
  have hA : 1 ≤ A := (global_parameter_scale hd P.card hP).1
  obtain ⟨hD, hAD⟩ := global_rank_degree_scale A hA
  change 1 ≤ D at hD
  change A ≤ 2 * (D : ℝ) at hAD
  have hp : p ∉ T := by
    intro hpT
    have hpp : (p, p) ∈ G := mem_pair_of_mem_star (hT hpT)
    exact (Finset.mem_offDiag.mp (hG.1 hpp)).2.2 rfl
  obtain ⟨V, hpoints, hkernel, hcomponents⟩ :=
    Bridges.projective_envelope d (starDirections p T) D
  obtain ⟨F, hF, hlocus⟩ := Request.homogeneous_envelope_carriers d hd D
    (Bridges.homogeneousEquations (starDirections p T) D)
    (fun f hf => hf.1) V hpoints
  have hdefined : ProjectiveFamily.ComponentsDefinedInDegree F D := by
    refine ⟨Bridges.homogeneousEquations (starDirections p T) D, ?_, ?_⟩
    · intro f hf
      exact ⟨D, le_rfl, hf.1⟩
    · intro Y hY
      exact hcomponents Y (hF Y hY).2.1
  have hinside : starDirections p T ⊆ V.points := by
    intro z hz
    rw [hpoints]
    intro f hf
    exact hf.2 z.rep ⟨z.rep_nonzero, by simpa only [Projectivization.mk_rep] using hz⟩
  have hcover := star_family_covers_partners p T hp V F hinside hlocus
  have hcount : ∀ Y ∈ F,
      ((T.filter fun q => DirMem Y p q).card : ℝ) ≤ C * (Y.degree : ℝ) * A ^ Y.dimension := by
    intro Y hY
    have hsub : T.filter (fun q => DirMem Y p q) ⊆ (star G p).filter (fun q => DirMem Y p q) := by
      intro q hq
      obtain ⟨hqT, hqY⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hT hqT, hqY⟩
    have hcard : ((T.filter fun q => DirMem Y p q).card : ℝ) ≤
        ((star G p).filter fun q => DirMem Y p q).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans (hcap p Y (hF Y hY).1)
  have hweight := star_rank_weighted_count p T F C A hC hA hcover hcount
  have hcompare := star_rank_weighted_compare F A hA D hD hAD
    (fun Y hY => ⟨(hF Y hY).1, (hF Y hY).2.2⟩)
  have hrank : starRank D p T = ProjectiveFamily.hilbert F D := by
    change starRank D p T = (ProjectiveFamily.locus F).hilbert D
    rw [hlocus]
    exact Bridges.starRank_eq_hilbert p T hp V (star_envelope_physical_kernel p T hp D V hkernel)
  have henvR : (c : ℝ) * (TrackA.projectiveWeightedDegree F D : ℝ) ≤ (starRank D p T : ℝ) := by
    have h : (c : ℝ) * (TrackA.projectiveWeightedDegree F D : ℝ) ≤
        (ProjectiveFamily.hilbert F D : ℝ) := by
      exact_mod_cast henv F D hD hdefined
    rwa [← hrank] at h
  have htotal : (c : ℝ) * (T.card : ℝ) ≤ (C * (2 : ℝ) ^ d) * (starRank D p T : ℝ) := by
    calc
      (c : ℝ) * (T.card : ℝ) ≤
          (c : ℝ) * (C * ∑ Y ∈ F, (Y.degree : ℝ) * A ^ Y.dimension) :=
            mul_le_mul_of_nonneg_left hweight hcR.le
      _ ≤ (c : ℝ) * (C * ((2 : ℝ) ^ d * (TrackA.projectiveWeightedDegree F D : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hcompare hC.le) hcR.le
      _ = (C * (2 : ℝ) ^ d) * ((c : ℝ) * (TrackA.projectiveWeightedDegree F D : ℝ)) := by ring
      _ ≤ (C * (2 : ℝ) ^ d) * (starRank D p T : ℝ) :=
            mul_le_mul_of_nonneg_left henvR hden.le
  change ((c : ℝ) / (C * (2 : ℝ) ^ d)) * (T.card : ℝ) ≤ (starRank D p T : ℝ)
  calc
    ((c : ℝ) / (C * (2 : ℝ) ^ d)) * (T.card : ℝ) =
        ((c : ℝ) * (T.card : ℝ)) / (C * (2 : ℝ) ^ d) := by ring
    _ ≤ (starRank D p T : ℝ) := (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)

/-- red:independent-stars (`reduction.tex:204-245`): a positive-density symmetric selection whose
stars have linearly independent direction evaluations at degree `⌊A⌋`. -/
theorem exists_selection_independentStars (hd : 3 ≤ d) (hIH : IH d) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ,
      ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ ε₀ * Ascale d P.card →
        ∃ S : Finset (RPoint d × RPoint d), IsSymmSelection P S ∧
          c * (P.card : ℝ) ^ 2 ≤ S.card ∧
          ∀ p : RPoint d, IndependentStar (testDegree d P.card) p (star S p) := by
  classical
  obtain ⟨c₀, c₁, hc₀, hc₁, ε₀, hε₀, N₀, hstarRank⟩ :=
    exists_selection_starRank hd hIH
  have hratio : 0 < c₁ / (c₁ + 2) := by positivity
  refine ⟨c₀ * (c₁ / (c₁ + 2)), mul_pos hc₀ hratio, ε₀, hε₀, N₀, ?_⟩
  intro P hN hM
  obtain ⟨G, hG, hGcard, hGstarRank⟩ := hstarRank P hN hM
  let vec : RPoint d → RPoint d →
      Module.Dual ℂ (MvPolynomial.homogeneousSubmodule (Fin d) ℂ (testDegree d P.card)) :=
    fun p q => homEval d (testDegree d P.card) (cplx (q - p))
  have hrank : ∀ p : RPoint d,
      ∀ T ⊆ (G.filter fun e => e.1 = p).image Prod.snd,
        c₁ * T.card ≤ Module.finrank ℂ (Submodule.span ℂ ((vec p) '' (T : Set (RPoint d)))) := by
    intro p T hT
    have h := hGstarRank p T (by simpa [star] using hT)
    have hRange : Set.range (fun q : T =>
        homEval d (testDegree d P.card) (cplx ((q : RPoint d) - p))) =
        (fun q : RPoint d => homEval d (testDegree d P.card) (cplx (q - p))) ''
          (T : Set (RPoint d)) := by
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨q, q.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    rw [starRank, hRange] at h
    simpa [vec] using h
  obtain ⟨S, hSG, hSsymm, hScard, hSindep⟩ :=
    exists_independent_selection G hG.2 vec c₁ hc₁ hrank
  have hSselection : IsSymmSelection P S := ⟨hSG.trans hG.1, hSsymm⟩
  have hSsize : c₀ * (c₁ / (c₁ + 2)) * (P.card : ℝ) ^ 2 ≤ S.card := by
    calc
      c₀ * (c₁ / (c₁ + 2)) * (P.card : ℝ) ^ 2 =
          (c₁ / (c₁ + 2)) * (c₀ * (P.card : ℝ) ^ 2) := by ring
      _ ≤ (c₁ / (c₁ + 2)) * G.card :=
        mul_le_mul_of_nonneg_left hGcard (le_of_lt hratio)
      _ ≤ S.card := hScard
  refine ⟨S, hSselection, ?_, ?_⟩
  · simpa [mul_assoc] using hSsize
  · intro p
    simpa [IndependentStar, star, vec] using hSindep p

end Reduction

end

end DistinctDistances
