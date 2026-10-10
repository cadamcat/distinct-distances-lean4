import DistinctDistances.TrackD.Profiles.Envelope
import DistinctDistances.TrackD.Profiles.Partition

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- A bounded linear combination can avoid every listed carrier at once.
The degree stays D even when the list and its later-selected point set grow. -/
theorem bounded_common_equation (T : Set (Point d)) (D : ℕ)
    (Zs : Finset (AffineVariety d))
    (hchoose : ∀ Z ∈ Zs, ∃ f : Poly d,
      f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D ∧ f ∉ Z.ideal) :
    ∃ g : Poly d, g ∈ MvPolynomial.vanishingIdeal ℂ T ∧ g.totalDegree ≤ D ∧
      ∀ Z ∈ Zs, g ∉ Z.ideal := by
  have hfor (i : Zs) : ∃ f : Poly d,
      f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D ∧ f ∉ i.val.ideal :=
    hchoose i.val i.property
  choose f hvan hdeg hnot using hfor
  have hpoints (i : Zs) : ∃ p ∈ i.val, MvPolynomial.eval p (f i) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot i ((mem_ideal_iff_eval_zero i.val (f i)).mpr h)
  choose p hp hfp using hpoints
  let L (i : Zs) : MvPolynomial Zs ℂ :=
    ∑ j : Zs, MvPolynomial.C (MvPolynomial.eval (p i) (f j)) * MvPolynomial.X j
  have hL (i : Zs) : L i ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (Pi.single i (1 : ℂ))) h
    have hval : MvPolynomial.eval (Pi.single i (1 : ℂ)) (L i) =
        MvPolynomial.eval (p i) (f i) := by
      simp [L, Pi.single_apply]
    rw [hval, map_zero] at he
    exact hfp i he
  have hprod : (∏ i : Zs, L i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hL i)
  have hex : ∃ c : Zs → ℂ, MvPolynomial.eval c (∏ i : Zs, L i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hprod
    apply MvPolynomial.funext
    intro c
    simpa using h c
  obtain ⟨c, hc⟩ := hex
  let g : Poly d := ∑ i : Zs, MvPolynomial.C (c i) * f i
  have hgvan : g ∈ MvPolynomial.vanishingIdeal ℂ T := by
    apply Submodule.sum_mem
    intro i _
    exact (MvPolynomial.vanishingIdeal ℂ T).mul_mem_left _ (hvan i)
  have hgdeg : g.totalDegree ≤ D := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hdeg i)
  refine ⟨g, hgvan, hgdeg, ?_⟩
  intro Z hZ hgZ
  let i : Zs := ⟨Z, hZ⟩
  have hci : MvPolynomial.eval c (L i) ≠ 0 := by
    rw [map_prod, Finset.prod_ne_zero_iff] at hc
    exact hc i (Finset.mem_univ i)
  have heval : MvPolynomial.eval (p i) g = MvPolynomial.eval c (L i) := by
    simp [g, L, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, mul_comm]
  have hz : MvPolynomial.eval (p i) g = 0 := hp i g hgZ
  exact hci (heval.symm.trans hz)

/-- An irreducible carrier contained in a finite union lies in one member.
The proof multiplies separating equations before invoking prime-ideal density. -/
theorem irreducible_subset_finite_union (V : AffineVariety d) (hV : V.IsIrreducible)
    (F : AffineFamily.Family d) (hVF : V.points ⊆ (AffineFamily.locus F).points) :
    ∃ W ∈ F, V.Subvariety W := by
  by_contra h
  have hex (W : F) : ∃ f : Poly d, f ∈ W.val.ideal ∧ f ∉ V.ideal := by
    by_contra hf
    apply h
    refine ⟨W.val, W.property, ?_⟩
    intro f hfW
    by_contra hfV
    exact hf ⟨f, hfW, hfV⟩
  choose f hfW hfV using hex
  have hprod : (∏ W : F, f W) ∈ V.ideal := (mem_ideal_iff_eval_zero V _).mpr (by
    intro x hx
    have hxF := hVF hx
    rw [AffineFamily.points_locus] at hxF
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hxF
    let i : F := ⟨W, hW⟩
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact hxW (f i) (hfW i))
  rcases hV.prod_mem_iff.mp hprod with ⟨W, _, hW⟩
  exact hfV W hW

def pathComponents (π : CutPath d) (j : ℕ) : AffineFamily.Family d :=
  let V := AffineVariety.ofIdeal (π.system j)
  Finset.univ.image (fun W : V.Component => W.variety)

theorem mem_pathComponents_iff (π : CutPath d) (j : ℕ) (Z : AffineVariety d) :
    Z ∈ pathComponents π j ↔ π.IsCarrier j Z := by
  constructor
  · intro hZ
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hZ
    change W.val ∈ (π.system j).minimalPrimes
    simpa only [AffineVariety.ofIdeal, Ideal.radical_minimalPrimes] using W.property
  · intro hZ
    change Z.ideal ∈ (π.system j).minimalPrimes at hZ
    let V := AffineVariety.ofIdeal (π.system j)
    let W : V.Component := ⟨Z.ideal, by
      simpa only [V, AffineVariety.ofIdeal, Ideal.radical_minimalPrimes] using hZ⟩
    have heq : W.variety = Z := AffineVariety.ext rfl
    exact Finset.mem_image.mpr ⟨W, Finset.mem_univ W, heq⟩

theorem exists_envelope_equation_proper (T : Set (Point d)) (D : ℕ)
    (Z : AffineVariety d) (hZ : ¬ Z.points ⊆ (envelope T D).points) :
    ∃ f : Poly d, f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D ∧ f ∉ Z.ideal := by
  by_contra h
  apply hZ
  apply (AffineVariety.subvariety_iff_points_subset Z (envelope T D)).mp
  have hspan : Ideal.span {f : Poly d | f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D} ≤
      Z.ideal := by
    apply Ideal.span_le.mpr
    intro f hf
    by_contra hfZ
    exact h ⟨f, hf.1, hf.2, hfZ⟩
  change (Ideal.span {f : Poly d | f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D}).radical ≤ Z.ideal
  have hr := Ideal.radical_mono hspan
  rwa [Z.isRadical.radical] at hr

def lowEnvelopePoints (X : Piece d) (S : Finset (Pt d)) (j D : ℕ) : Finset (Pt d) :=
  S.filter (fun x => ∀ V ∈ envelopeComponents (toC '' (S : Set (Pt d))) D,
    d - j ≤ V.dimension → toC x ∉ V)

/-- `profiles.tex:283–290`: low-dimensional envelope components capture
only the no-capture allowance. The proper equation is a bounded linear
combination, so its degree has no dependence on the later subset S. -/
theorem low_envelope_points_bound (P : Finset (Pt d)) (X : Piece d)
    (θ ξ K : ℝ) (hK : 1 ≤ K) (hX : PieceGood P θ ξ K X)
    (j : ℕ) (hj : j < d) (b : ℝ) (hb : OnPlateau X.path.time j ξ b)
    (hT : 1 ≤ testDeg (cfgB P) X.width b)
    (S : Finset (Pt d)) (hS : S ⊆ X.pts) :
    ((lowEnvelopePoints X S j ⌊testDeg (cfgB P) X.width b⌋₊).card : ℝ) ≤ θ * X.pts.card := by
  let D := ⌊testDeg (cfgB P) X.width b⌋₊
  let T := toC '' (S : Set (Pt d))
  let E := envelope T D
  let Zs := (pathComponents X.path j).filter (fun Z => ¬ Z.points ⊆ E.points)
  obtain ⟨g, hgvan, hgdeg, hgproper⟩ := bounded_common_equation T D Zs (by
    intro Z hZ
    exact exists_envelope_equation_proper T D Z (Finset.mem_filter.mp hZ).2)
  have hdegree : (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) X.width b := by
    have hfloor : (D : ℝ) ≤ testDeg (cfgB P) X.width b := Nat.floor_le (by linarith)
    have hdegR : (g.totalDegree : ℝ) ≤ D := by exact_mod_cast hgdeg
    exact hdegR.trans (hfloor.trans (le_mul_of_one_le_left (by linarith) hK))
  have hcaptured := hX.noCapture j hj b hb hT g hdegree
  have hsubset : lowEnvelopePoints X S j D ⊆ X.path.captured j X.pts g := by
    intro x hx
    obtain ⟨hxS, hxlow⟩ := Finset.mem_filter.mp hx
    have hxX := hS hxS
    apply Finset.mem_filter.mpr
    refine ⟨hxX, ?_, ?_⟩
    · exact hgvan (toC x) ⟨x, hxS, rfl⟩
    · intro Z hZ
      obtain ⟨hZi, hZd⟩ := prof_partition_pure X x hxX (hX.vanish x hxX)
        (hX.proper x hxX) j hj.le Z hZ
      have hnot : ¬ Z.points ⊆ E.points := by
        intro hZE
        have hEnv : AffineFamily.locus (envelopeComponents T D) = E := component_family_locus E
        obtain ⟨V, hV, hZV⟩ := irreducible_subset_finite_union Z hZi
          (envelopeComponents T D) (by simpa only [hEnv] using hZE)
        have hdim : d - j ≤ V.dimension := by
          rw [← hZd]
          obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hV
          exact irreducible_dimension_mono Z W.variety hZi W.irreducible hZV
        have hxV : toC x ∈ V := (AffineVariety.subvariety_iff_points_subset Z V).mp hZV hZ.2
        exact hxlow V hV hdim hxV
      exact hgproper Z (Finset.mem_filter.mpr ⟨(mem_pathComponents_iff X.path j Z).mpr hZ.1, hnot⟩)
  have hcard := Finset.card_le_card hsubset
  have hcardR : ((lowEnvelopePoints X S j D).card : ℝ) ≤ ((X.path.captured j X.pts g).card : ℝ) :=
    by exact_mod_cast hcard
  exact hcardR.trans hcaptured

/-- Choose one envelope dimension carrying a fixed fraction of the later
subset. The fraction 1/(d+1) and the loss θ are independent of that choice. -/
theorem dense_envelope_group (X : Piece d) (S : Finset (Pt d)) (j D : ℕ)
    (hj : j ≤ d) (θ : ℝ)
    (hlow : ((lowEnvelopePoints X S j D).card : ℝ) ≤ θ * X.pts.card)
    (hpos : θ * X.pts.card < (S.card : ℝ)) :
    ∃ (h : ℕ) (F : AffineFamily.Family d) (S' : Finset (Pt d)),
      d - j ≤ h ∧ h ≤ d ∧ F ⊆ envelopeComponents (toC '' (S : Set (Pt d))) D ∧
      AffineFamily.IsPure F h ∧ S' ⊆ S ∧
      ((S.card : ℝ) - θ * X.pts.card) / (d + 1 : ℝ) ≤ S'.card ∧
      toC '' (S' : Set (Pt d)) ⊆ (AffineFamily.locus F).points := by
  let E := envelopeComponents (toC '' (S : Set (Pt d))) D
  let low := lowEnvelopePoints X S j D
  let high := S \ low
  let block (h : Fin (d+1)) : Finset (Pt d) :=
    if d - j ≤ h.val then S.filter (fun x => ∃ V ∈ E, V.dimension = h.val ∧ toC x ∈ V) else ∅
  have hE : ∀ V ∈ E, V.IsIrreducible ∧ V.dimension ≤ d := by
    intro V hV
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨W.irreducible, dimension_le_ambient W.variety W.irreducible⟩
  have hcover : high ⊆ Finset.univ.biUnion block := by
    intro x hx
    obtain ⟨hxS, hxlow⟩ := Finset.mem_sdiff.mp hx
    have hn : ¬ ∀ V ∈ E, d - j ≤ V.dimension → toC x ∉ V := by
      intro h
      exact hxlow (Finset.mem_filter.mpr ⟨hxS, h⟩)
    push Not at hn
    obtain ⟨V, hV, hdim, hxV⟩ := hn
    let h : Fin (d+1) := ⟨V.dimension, by have := (hE V hV).2; omega⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨h, Finset.mem_univ h, ?_⟩
    dsimp only [block]
    rw [if_pos hdim]
    exact Finset.mem_filter.mpr ⟨hxS, V, hV, rfl, hxV⟩
  have hsumN : high.card ≤ ∑ h : Fin (d+1), (block h).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hsumR : (high.card : ℝ) ≤ ∑ h : Fin (d+1), ((block h).card : ℝ) := by
    exact_mod_cast hsumN
  have hlowS : low ⊆ S := Finset.filter_subset _ _
  have hcard : high.card + low.card = S.card := by
    change (S \ low).card + low.card = S.card
    rw [Finset.card_sdiff_of_subset hlowS]
    exact Nat.sub_add_cancel (Finset.card_le_card hlowS)
  have hcardR : (high.card : ℝ) + low.card = S.card := by exact_mod_cast hcard
  let mass : ℝ := (S.card : ℝ) - θ * X.pts.card
  have hmass : mass ≤ ∑ h : Fin (d+1), ((block h).card : ℝ) := by
    dsimp [mass]
    linarith
  have hden : (0 : ℝ) < d + 1 := by positivity
  have hex : ∃ h : Fin (d+1), mass / (d + 1 : ℝ) ≤ (block h).card := by
    by_contra h
    push Not at h
    have hslt : (∑ i : Fin (d+1), ((block i).card : ℝ)) <
        ∑ _i : Fin (d+1), mass / (d + 1 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact (h i).le
      · exact ⟨0, Finset.mem_univ 0, h 0⟩
    have hconst : (∑ _i : Fin (d+1), mass / (d + 1 : ℝ)) = mass := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
    linarith
  obtain ⟨h, havg⟩ := hex
  have hmasspos : 0 < mass := sub_pos.mpr hpos
  have hblockpos : 0 < ((block h).card : ℝ) := (div_pos hmasspos hden).trans_le havg
  have hdim : d - j ≤ h.val := by
    by_contra hn
    have he : block h = ∅ := by dsimp only [block]; rw [if_neg hn]
    simp only [he, Finset.card_empty, Nat.cast_zero] at hblockpos
    linarith
  let F := E.filter (fun V => V.dimension = h.val)
  have hF : AffineFamily.IsPure F h.val := by
    intro V hV
    obtain ⟨hVE, hVd⟩ := Finset.mem_filter.mp hV
    exact ⟨(hE V hVE).1, hVd⟩
  refine ⟨h.val, F, block h, hdim, by omega, Finset.filter_subset _ _, hF, ?_, havg, ?_⟩
  · dsimp only [block]
    rw [if_pos hdim]
    exact Finset.filter_subset _ _
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    dsimp only [block] at hx
    rw [if_pos hdim] at hx
    obtain ⟨hxS, V, hV, hVd, hxV⟩ := Finset.mem_filter.mp hx
    rw [AffineFamily.points_locus]
    exact Set.mem_iUnion₂.mpr ⟨V, Finset.mem_filter.mpr ⟨hV, hVd⟩, hxV⟩

end
end DistinctDistances.TrackD
