import DistinctDistances.TrackE.OuterRowsData
import DistinctDistances.TrackE.CommonChartGraphMass
import DistinctDistances.TrackE.CommonLabelEnvelope
import DistinctDistances.TrackE.CommonProductLists
import DistinctDistances.TrackE.MOFlatAux
import DistinctDistances.TrackE.MOChartAux
import DistinctDistances.TrackE.SecantImageAux
import DistinctDistances.TrackE.CommonCertificateSupport
import DistinctDistances.TrackD.RationalImages

/-! The retained outer pool with its fixed image family (sparse-cones.tex:340–424).

`outer_lowspan_carrier_count` (sc:382–390) bounds the distinct carriers of
small affine span; `outer_pool_shrink` deletes their points (chart-free pool
data); `outer_chart_restriction` fixes one direction chart and restricts the
covered graph with its image family (a dense chart piece cannot exist
globally, so the chain runs per chart and the assembly combines `d` charts);
`outer_carrier_regular` records smoothness and uniqueness of the owner at a
retained point. (For `k = 1` the identification with the global terminal
assignment, sc:415–424, is the field `CommonPhysicalSequence.terminal`.) -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The chart-free retained outer pool at index `i`: a large subpool `S`, the
fixed carrier-pair family `R` with its owner map, covering every selected
incidence. `j` is the zero-based cut before the final plateau
(`k = d - (j+1)`). -/
structure OuterPoolData {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (M : CommonPoolProfile T) (k i j : ℕ) (ρ ε : ℝ) where
  S : Finset (RPoint d)
  R : Finset (AffineVariety d × AffineVariety d)
  own : TrackD.Pt d → AffineVariety d
  hkj : k + j + 1 = d
  hSsub : S ⊆ TrackD.poolPts (T.sources i)
  hScard : (1 - ρ) * ((TrackD.poolPts (T.sources i)).card : ℝ) ≤ (S.card : ℝ)
  hownsup : TrackD.CarrierAssignment (T.sources i ∪ T.targets i) (j + 1) own
  hRirr : ∀ r ∈ R, r.1.IsIrreducible ∧ r.2.IsIrreducible
  hRdim : ∀ r ∈ R, r.1.dimension = k ∧ r.2.dimension = k
  hownfull : ∀ pq ∈ outerSelectedGraph T i, ∃ r ∈ R, own pq.1 = r.1 ∧ own pq.2 = r.2
  hspan : 2 ≤ k → ∀ q ∈ S, ¬ ∃ Ff : AffineSubspace ℂ (Point d),
    Module.finrank ℂ Ff.direction ≤ k + 1 ∧ (own q).points ⊆ ↑Ff

/-- One chart piece of the retained pool: the subgraph `G` in direction chart
`i₀` with a pure `2k`-dimensional image family `U` (degree bound) containing
the complete owner image of every pair of `G`, labels on those images, and
the image-mass bound for later subfamilies (the form of
`selected_common_chart_graph_mass`). The deletion `hGdel` is absolute
(`≤ ρ'·|S|²`); the assembly unions the `d` charts. -/
structure OuterChartCert {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (M : CommonPoolProfile T) (k i j : ℕ) (i₀ : Fin d) (ρ ε ρ' τ : ℝ) where
  pool : OuterPoolData T M k i j ρ ε
  W : CommonPhysicalSequence T M (j + 1) τ
  L : CommonProductLists W (ε / 2)
  hWownF : ∀ q : TrackD.Pt d, W.owner i q = pool.own q
  G : Finset (RPoint d × RPoint d)
  U : Finset (AffineVariety (d + d))
  hGsub : G ⊆ outerSelectedGraph T i
  hGmem : ∀ pq ∈ G, pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S
  hchart : ∀ pq ∈ G, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0
  hGdel : (((outerSelectedGraph T i).filter (fun pq =>
    (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)) \ G).card ≤
    ρ' * (pool.S.card : ℝ) ^ 2
  hU : ∀ W ∈ U, W.IsIrreducible ∧ W.dimension = 2 * k
  hUdeg : ((AffineFamily.degree U : ℚ) : ℝ) ≤
    (1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
      Real.exp (ε * M.s i)
  hUmem : ∀ pq ∈ G, commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ U
  hlabel : ∀ pq ∈ G, (fun kk =>
    TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
      (finSumFinEquiv.symm kk)) ∈
        (commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)).points
  hown : ∀ pq ∈ G, ∃ r ∈ pool.R, pool.own pq.1 = r.1 ∧ pool.own pq.2 = r.2
  hGpoolsList : ∀ pq ∈ G, pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
    W.owner i pq.2 ∈ L.lists i (W.owner i pq.1)
  hmassW : ∀ J : Finset (AffineVariety (d + d)), J ⊆ U →
    ((G.filter (fun pq =>
      commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ J)).card : ℝ) ≤
      Real.exp (ε * M.s i) * (((W.sources i).card : ℝ) * (W.targets i).card /
        (commonCarrierScale M (j + 1) i) ^ 2) *
        ((∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
          (Z.degree : ℚ)) : ℝ)

/-- A chart certificate at a smaller deletion budget is one at a larger budget. -/
def OuterChartCert.mono {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {k i j : ℕ} {i₀ : Fin d} {ρ ε ρ₁ ρ₂ τ : ℝ}
    (c : OuterChartCert T M k i j i₀ ρ ε ρ₁ τ) (h : ρ₁ ≤ ρ₂) :
    OuterChartCert T M k i j i₀ ρ ε ρ₂ τ :=
  { c with
    hGdel := c.hGdel.trans (mul_le_mul_of_nonneg_right h (sq_nonneg _)) }

/-- sc:outer-pool.low-span count (sparse-cones.tex:382–390).
Distinct owner-carriers whose affine span has dimension at most `k+1` number at
most `e_j exp(εs)`. Inputs: the per-piece degree budgets
(`common_piece_limiting_budgets`, CommonCarrierBudgets.lean) and the owner-fiber
counting (`selected_common_carrier_budgets`, same file); the pool has at most
`exp(o(s))` pieces. `W` lives at the final-plateau index `d - k`. -/
theorem outer_lowspan_carrier_count {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k : ℕ) {τ : ℝ} (W : CommonPhysicalSequence T M (d - k) τ) (hk : 1 ≤ k ∧ k + 1 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ C : Finset (AffineVariety d),
      (∀ X ∈ C, ∃ Ff : AffineSubspace ℂ (Point d),
        Module.finrank ℂ Ff.direction ≤ k + 1 ∧ X.points ⊆ ↑Ff) ∧
      ((C.card : ℝ)) ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
        Real.exp (ε * M.s i) ∧
      ∀ q : RPoint d, q ∈ TrackD.poolPts (T.sources i) →
        (∃ Ff : AffineSubspace ℂ (Point d), Module.finrank ℂ Ff.direction ≤ k + 1 ∧
          (W.owner i q).points ⊆ ↑Ff) → W.owner i q ∈ C := by
  classical
  have hj : d - k ≤ d := Nat.sub_le d k
  have hη : 0 < ε / 2 := half_pos hε
  have hθ : 0 < ε / 2 := half_pos hε
  have heta : ε / 2 + ε / 2 = ε := add_halves ε
  filter_upwards [common_piece_limiting_budgets M (d - k) hj (ε / 2) hη,
    M.good (ε / 2) hθ 1 (by norm_num) 1 le_rfl 1 (by norm_num)] with i hpiece hgood
  -- the union of all source piece families, filtered to low-span
  set U : Finset (AffineVariety d) :=
    (T.sources i).biUnion (fun X => TrackD.pieceCarrierFamily X (d - k)) with hUdef
  set C : Finset (AffineVariety d) := U.filter
    (fun X => ∃ Ff : AffineSubspace ℂ (Point d),
      Module.finrank ℂ Ff.direction ≤ k + 1 ∧ X.points ⊆ ↑Ff) with hCdef
  refine ⟨C, ?_, ?_, ?_⟩
  · intro X hX
    simp only [hCdef, Finset.mem_filter] at hX
    exact hX.2
  · -- card bound via degree sums and piece count
    have hCsubU : C ⊆ U := Finset.filter_subset _ _
    have hUcard_le : (U.card : ℝ) ≤
        ∑ X ∈ T.sources i, ((TrackD.pieceCarrierFamily X (d - k)).card : ℝ) := by
      have hnat : U.card ≤
          ∑ X ∈ T.sources i, (TrackD.pieceCarrierFamily X (d - k)).card := by
        simpa only [hUdef] using Finset.card_biUnion_le
      exact_mod_cast hnat
    have hdeg_one : ∀ X ∈ T.sources i, ∀ Z ∈ TrackD.pieceCarrierFamily X (d - k),
        (1 : ℝ) ≤ (Z.degree : ℝ) := by
      intro X hXmem Z hZmem
      obtain ⟨hcarr, q, hq, hqZ⟩ :=
        (TrackD.mem_pieceCarrierFamily X (d - k) Z).mp hZmem
      have hXunion : X ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hXmem
      have hgoodX := hgood.1.pieces X hXmem
      -- hgoodX is PieceGood; extract vanish/proper via its fields
      have hvan : ∀ a : Fin d,
          MvPolynomial.eval (TrackD.toC q) (X.path.cut a) = 0 :=
        fun a => hgoodX.vanish q hq a
      have hprop : X.path.ProperAt (TrackD.toC q) := hgoodX.proper q hq
      have hirr : Z.IsIrreducible :=
        (TrackD.prof_partition_pure X q hq hvan hprop (d - k) hj Z
          ⟨hcarr, hqZ⟩).1
      have hle : (1 : ℚ) ≤ Z.degree := AffineVariety.one_le_degree Z hirr.ne_top
      exact_mod_cast hle
    have hfam_card_le : ∀ X ∈ T.sources i,
        ((TrackD.pieceCarrierFamily X (d - k)).card : ℝ) ≤
        ∑ Z ∈ TrackD.pieceCarrierFamily X (d - k), (Z.degree : ℝ) := by
      intro X hXmem
      calc ((TrackD.pieceCarrierFamily X (d - k)).card : ℝ)
          = ∑ _Z ∈ TrackD.pieceCarrierFamily X (d - k), (1 : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ Z ∈ TrackD.pieceCarrierFamily X (d - k), (Z.degree : ℝ) :=
            Finset.sum_le_sum (fun Z hZ => hdeg_one X hXmem Z hZ)
    have hsum_le : ∑ X ∈ T.sources i,
        ((TrackD.pieceCarrierFamily X (d - k)).card : ℝ) ≤
        ∑ X ∈ T.sources i, ∑ Z ∈ TrackD.pieceCarrierFamily X (d - k),
          (Z.degree : ℝ) :=
      Finset.sum_le_sum hfam_card_le
    have hpiece_sum : ∀ X ∈ T.sources i,
        (∑ Z ∈ TrackD.pieceCarrierFamily X (d - k), (Z.degree : ℝ)) ≤
        commonCarrierScale M (d - k) i * Real.exp ((ε / 2) * M.s i) := by
      intro X hXmem
      have hXunion : X ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hXmem
      exact (hpiece X hXunion).1
    have htotal : ∑ X ∈ T.sources i, ∑ Z ∈ TrackD.pieceCarrierFamily X (d - k),
        (Z.degree : ℝ) ≤
        commonCarrierScale M (d - k) i * Real.exp (ε * M.s i) := by
      have hcount : ((T.sources i).card : ℝ) ≤ Real.exp ((ε / 2) * M.s i) :=
        hgood.1.count
      have he_pos : 0 < commonCarrierScale M (d - k) i := by
        unfold commonCarrierScale TrackD.eScale TrackD.cutScale TrackD.testDeg
        exact Finset.prod_pos fun _ _ =>
          mul_pos (regime.B_pos i) (Real.exp_pos _)
      have hexp_pos : 0 < Real.exp ((ε / 2) * M.s i) := Real.exp_pos _
      calc ∑ X ∈ T.sources i, ∑ Z ∈ TrackD.pieceCarrierFamily X (d - k),
            (Z.degree : ℝ)
          ≤ ∑ _X ∈ T.sources i, commonCarrierScale M (d - k) i *
              Real.exp ((ε / 2) * M.s i) :=
            Finset.sum_le_sum hpiece_sum
        _ = ((T.sources i).card : ℝ) * (commonCarrierScale M (d - k) i *
              Real.exp ((ε / 2) * M.s i)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Real.exp ((ε / 2) * M.s i) * (commonCarrierScale M (d - k) i *
              Real.exp ((ε / 2) * M.s i)) :=
            mul_le_mul_of_nonneg_right hcount (mul_nonneg he_pos.le hexp_pos.le)
        _ = commonCarrierScale M (d - k) i * Real.exp (ε * M.s i) := by
            have hexp_add : Real.exp ((ε / 2) * M.s i) *
                Real.exp ((ε / 2) * M.s i) = Real.exp (ε * M.s i) := by
              rw [← Real.exp_add]
              congr 1
              linarith [heta]
            calc Real.exp ((ε / 2) * M.s i) * (commonCarrierScale M (d - k) i *
                Real.exp ((ε / 2) * M.s i))
                = commonCarrierScale M (d - k) i *
                  (Real.exp ((ε / 2) * M.s i) * Real.exp ((ε / 2) * M.s i)) := by
                  ring
              _ = commonCarrierScale M (d - k) i * Real.exp (ε * M.s i) := by
                  rw [hexp_add]
    have hCcard : (C.card : ℝ) ≤
        commonCarrierScale M (d - k) i * Real.exp (ε * M.s i) := by
      calc (C.card : ℝ) ≤ (U.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hCsubU
        _ ≤ ∑ X ∈ T.sources i, ((TrackD.pieceCarrierFamily X (d - k)).card : ℝ) :=
            hUcard_le
        _ ≤ ∑ X ∈ T.sources i, ∑ Z ∈ TrackD.pieceCarrierFamily X (d - k),
              (Z.degree : ℝ) := hsum_le
        _ ≤ commonCarrierScale M (d - k) i * Real.exp (ε * M.s i) := htotal
    simpa only [commonCarrierScale] using hCcard
  · intro q hqP hex
    simp only [hCdef, Finset.mem_filter]
    constructor
    · -- owner lies in the union
      obtain ⟨Xpiece, hXmem, hqmem⟩ := Finset.mem_biUnion.mp hqP
      have hXunion : Xpiece ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hXmem
      obtain ⟨hcarr, hpt⟩ := W.supported i Xpiece hXunion q hqmem
      have hmemFam : W.owner i q ∈ TrackD.pieceCarrierFamily Xpiece (d - k) := by
        rw [TrackD.mem_pieceCarrierFamily]
        exact ⟨hcarr, q, hqmem, hpt⟩
      simp only [hUdef, Finset.mem_biUnion]
      exact ⟨Xpiece, hXmem, hmemFam⟩
    · exact hex

/-- sc:outer-pool.carrier-regularity (sparse-cones.tex:541, 615, 632–634).
At a retained point (`p ∈ W.sources i ∪ W.targets i`) the owner is smooth and
is the unique carrier of the full original family through `p` (paper: "unique
member of the full physical family at p", sc:615; "uniqueness ... forces
Y = X", sc:632). Both come from `TrackD.JacRegularAt` in the definition of the
retained pool. -/
theorem outer_carrier_regular {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    {jW : ℕ} {τ : ℝ} (W : CommonPhysicalSequence T M jW τ)
    (k : ℕ) (i : ℕ) (p : RPoint d) (X : AffineVariety d)
    (hp : p ∈ W.sources i ∪ W.targets i)
    (hX : X.IsIrreducible ∧ X.dimension = k)
    (hmem : TrackD.toC p ∈ X.points)
    (hown : W.owner i p = X) :
    X.IsSmoothAt (TrackD.toC p) ∧
      ∀ Y : AffineVariety d, TrackD.PoolCarrier (T.sources i ∪ T.targets i) jW Y →
        Y.IsIrreducible → Y.dimension = k → TrackD.toC p ∈ Y.points → Y = X := by
  have hcase : ∃ pl : Finset (TrackD.Piece d), pl ⊆ T.sources i ∪ T.targets i ∧
      p ∈ TrackD.poolPts pl ∧ TrackD.JacRegularAt (T.sources i ∪ T.targets i) jW
        (W.equations i) (W.minor i) (TrackD.toC p) := by
    rcases Finset.mem_union.mp hp with h | h
    · simp only [CommonPhysicalSequence.sources, retainedCommonPool, Finset.mem_filter] at h
      exact ⟨T.sources i, Finset.subset_union_left, h.1, h.2.1⟩
    · simp only [CommonPhysicalSequence.targets, retainedCommonPool, Finset.mem_filter] at h
      exact ⟨T.targets i, Finset.subset_union_right, h.1, h.2.1⟩
  obtain ⟨pl, hpl, hppool, hreg⟩ := hcase
  obtain ⟨_, Z, ⟨_, _⟩, huniq, hsm, _⟩ := hreg
  obtain ⟨Xp, hXp, hpXp⟩ := Finset.mem_biUnion.mp hppool
  obtain ⟨hcarr, hpown⟩ := W.supported i Xp (hpl hXp) p hpXp
  have hownZ : W.owner i p = Z := huniq _ ⟨⟨Xp, hpl hXp, hcarr, p, hpXp, hpown⟩, hpown⟩
  have hXZ : X = Z := hown.symm.trans hownZ
  subst hXZ
  refine ⟨hsm, ?_⟩
  intro Y hY _ _ hpY
  exact huniq Y ⟨hY, hpY⟩

/-- sc:outer-pool.shrink (sparse-cones.tex:392–412). Delete
the points assigned to small-span carriers; the fixed carrier-pair family `R`
is built from the owner map (with the full `hownfull` linkage over the whole
selected graph). The per-flat sample cap `cap` comes from
`card_inter_proper_flat_le` (TrackE/FlatCaps.lean); the numeric deletion bound
`hdel` (carrier count times cap) is proved in the assembly from the degree
budgets, so this lemma is pure construction + counting. For `k ≥ 2` delete
every pool point whose owner lies in `C` (this gives `hspan` via `hsmall`);
no deletion is made when `k = 1`. Chart-specific data (images, graphs) is built
per chart in 187c. -/
theorem outer_pool_shrink {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    {j jW : ℕ} {τ : ℝ} (W : CommonPhysicalSequence T M jW τ)
    (k : ℕ) (hk : 1 ≤ k ∧ k + 1 < d) (hkj : k + j + 1 = d)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (i : ℕ)
    (own : TrackD.Pt d → AffineVariety d)
    (hownsup : TrackD.CarrierAssignment (T.sources i ∪ T.targets i) (j + 1) own)
    (hownW : ∀ q : TrackD.Pt d, W.owner i q = own q)
    (C : Finset (AffineVariety d))
    (hCcount : ((C.card : ℝ)) ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
        Real.exp (ε * M.s i))
    (cap : ℝ) (hcap0 : 0 ≤ cap)
    (hcap : ∀ X ∈ C, ∃ Ff : AffineSubspace ℂ (Point d),
      X.points ⊆ ↑Ff ∧ (((TrackD.poolPts (T.sources i)).filter
        (fun q => TrackD.toC q ∈ Ff)).card : ℝ) ≤ cap)
    (hdel : (C.card : ℝ) * cap ≤
      ρ * ((TrackD.poolPts (T.sources i)).card : ℝ))
    (hsmall : ∀ q : RPoint d, q ∈ TrackD.poolPts (T.sources i) →
      (∃ Ff : AffineSubspace ℂ (Point d), Module.finrank ℂ Ff.direction ≤ k + 1 ∧
        (W.owner i q).points ⊆ ↑Ff) → W.owner i q ∈ C) :
    Nonempty (OuterPoolData T M k i j ρ ε) := by
  classical
  set P : Finset (RPoint d) := TrackD.poolPts (T.sources i) with hPdef
  let Ff : AffineVariety d → AffineSubspace ℂ (Point d) := fun X =>
    if h : X ∈ C then Classical.choose (hcap X h) else ⊤
  have hFfsub : ∀ X ∈ C, X.points ⊆ ↑(Ff X) := by
    intro X hX
    have hspec := Classical.choose_spec (hcap X hX)
    simp only [Ff, dif_pos hX] at *
    exact hspec.1
  have hFfcap : ∀ X ∈ C, (((P.filter
      (fun q => TrackD.toC q ∈ Ff X)).card : ℝ)) ≤ cap := by
    intro X hX
    have hspec := Classical.choose_spec (hcap X hX)
    have hFfeq : Ff X = Classical.choose (hcap X hX) := by
      simp only [Ff, dif_pos hX]
    rw [hFfeq]
    have hPeq : P = TrackD.poolPts (T.sources i) := hPdef.symm
    -- hspec.2 is for the original pool filter; P is definitionally that pool
    simpa only [hPeq] using hspec.2
  set D : Finset (RPoint d) := P.filter (fun q => 2 ≤ k ∧ own q ∈ C) with hDdef
  set S : Finset (RPoint d) := P \ D with hSdef
  set R : Finset (AffineVariety d × AffineVariety d) :=
    (outerSelectedGraph T i).image (fun pq => (own pq.1, own pq.2)) with hRdef
  have hj1le : j + 1 ≤ d := by omega
  have hdim_eq : d - (j + 1) = k := by omega
  have hpiece_good : ∀ X ∈ T.sources i ∪ T.targets i,
      TrackD.PieceGood (regime.P i) (selectionTolerance (T.precision i))
        (selectionTolerance (T.precision i)) (selectionScale (T.precision i)) X := by
    intro X hX
    have hmem : X ∈ (T.partition i).pieces := by
      rcases Finset.mem_union.mp hX with h | h
      · exact (T.certificate i).sources_subset h
      · exact (T.certificate i).targets_subset h
    exact ((T.certificate i).good.pieces_good X hmem).1
  have hown_pure : ∀ q : RPoint d, ∀ X : TrackD.Piece d,
      X ∈ T.sources i ∪ T.targets i → q ∈ X.pts →
      (own q).IsIrreducible ∧ (own q).dimension = k := by
    intro q X hXmem hqmem
    obtain ⟨hcarr, hpt⟩ := hownsup X hXmem q hqmem
    have hgood := hpiece_good X hXmem
    have hvan : ∀ a : Fin d, MvPolynomial.eval (TrackD.toC q) (X.path.cut a) = 0 :=
      fun a => hgood.vanish q hqmem a
    have hprop : X.path.ProperAt (TrackD.toC q) := hgood.proper q hqmem
    have hlocal : own q ∈ X.path.localCarriers (j + 1) (TrackD.toC q) :=
      ⟨hcarr, hpt⟩
    have hpure := TrackD.prof_partition_pure X q hqmem hvan hprop
      (j + 1) hj1le (own q) hlocal
    rw [hdim_eq] at hpure
    exact hpure
  have hDsubP : D ⊆ P := Finset.filter_subset _ _
  have hSsubP : S ⊆ P := Finset.sdiff_subset
  have hDcover : D ⊆ C.biUnion (fun X => P.filter (fun q => TrackD.toC q ∈ Ff X)) := by
    intro q hqD
    simp only [hDdef, Finset.mem_filter] at hqD
    obtain ⟨hqP, hk2, hownC⟩ := hqD
    obtain ⟨Xpiece, hXmem, hqmem⟩ := Finset.mem_biUnion.mp hqP
    have hXunion : Xpiece ∈ T.sources i ∪ T.targets i :=
      Finset.mem_union_left _ hXmem
    obtain ⟨hcarr, hpt⟩ := hownsup Xpiece hXunion q hqmem
    have hsub := hFfsub (own q) hownC
    have hmemFf : TrackD.toC q ∈ Ff (own q) := hsub hpt
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨own q, hownC, hqP, hmemFf⟩
  have hDcard_le : (D.card : ℝ) ≤ (C.card : ℝ) * cap := by
    have h1 : D.card ≤
        (C.biUnion (fun X => P.filter (fun q => TrackD.toC q ∈ Ff X))).card :=
      Finset.card_le_card hDcover
    have hnat : (C.biUnion
        (fun X => P.filter (fun q => TrackD.toC q ∈ Ff X))).card ≤
        ∑ X ∈ C, (P.filter (fun q => TrackD.toC q ∈ Ff X)).card :=
      Finset.card_biUnion_le
    have h2 : ((C.biUnion
        (fun X => P.filter (fun q => TrackD.toC q ∈ Ff X))).card : ℝ) ≤
        ∑ X ∈ C, ((P.filter (fun q => TrackD.toC q ∈ Ff X)).card : ℝ) := by
      exact_mod_cast hnat
    have h3 : ∑ X ∈ C, ((P.filter (fun q => TrackD.toC q ∈ Ff X)).card : ℝ) ≤
        (C.card : ℝ) * cap := by
      have hle : ∀ X ∈ C, ((P.filter
          (fun q => TrackD.toC q ∈ Ff X)).card : ℝ) ≤ cap :=
        fun X hX => hFfcap X hX
      calc ∑ X ∈ C, ((P.filter (fun q => TrackD.toC q ∈ Ff X)).card : ℝ)
          ≤ ∑ X ∈ C, cap := Finset.sum_le_sum hle
        _ = (C.card : ℝ) * cap := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc (D.card : ℝ) ≤ ((C.biUnion
          (fun X => P.filter (fun q => TrackD.toC q ∈ Ff X))).card : ℝ) := by
            exact_mod_cast h1
      _ ≤ ∑ X ∈ C, ((P.filter (fun q => TrackD.toC q ∈ Ff X)).card : ℝ) := h2
      _ ≤ (C.card : ℝ) * cap := h3
  have hSDcard : S.card + D.card = P.card :=
    Finset.card_sdiff_add_card_eq_card hDsubP
  have hScard_real : (1 - ρ) * (P.card : ℝ) ≤ (S.card : ℝ) := by
    have hDle : (D.card : ℝ) ≤ ρ * (P.card : ℝ) :=
      le_trans hDcard_le hdel
    have hSDreal : (S.card : ℝ) + (D.card : ℝ) = (P.card : ℝ) := by
      exact_mod_cast hSDcard
    linarith
  have hgraph_mem : ∀ pq ∈ outerSelectedGraph T i,
      pq.1 ∈ P ∧ pq.2 ∈ TrackD.poolPts (T.targets i) := by
    intro pq hpq
    simp only [outerSelectedGraph, Finset.mem_filter, Finset.mem_product] at hpq
    exact ⟨hpq.1.1, hpq.1.2⟩
  have hRpure : ∀ r ∈ R,
      r.1.IsIrreducible ∧ r.1.dimension = k ∧
      r.2.IsIrreducible ∧ r.2.dimension = k := by
    intro r hr
    simp only [hRdef, Finset.mem_image] at hr
    obtain ⟨pq, hpq, rfl⟩ := hr
    have ⟨h1P, h2P⟩ := hgraph_mem pq hpq
    obtain ⟨X1, hX1mem, hq1mem⟩ := Finset.mem_biUnion.mp h1P
    have hX1union : X1 ∈ T.sources i ∪ T.targets i :=
      Finset.mem_union_left _ hX1mem
    have hpure1 := hown_pure pq.1 X1 hX1union hq1mem
    obtain ⟨X2, hX2mem, hq2mem⟩ := Finset.mem_biUnion.mp h2P
    have hX2union : X2 ∈ T.sources i ∪ T.targets i :=
      Finset.mem_union_right _ hX2mem
    have hpure2 := hown_pure pq.2 X2 hX2union hq2mem
    exact ⟨hpure1.1, hpure1.2, hpure2.1, hpure2.2⟩
  have hRirr : ∀ r ∈ R, r.1.IsIrreducible ∧ r.2.IsIrreducible := by
    intro r hr
    obtain ⟨h1, _, h2, _⟩ := hRpure r hr
    exact ⟨h1, h2⟩
  have hRdim : ∀ r ∈ R, r.1.dimension = k ∧ r.2.dimension = k := by
    intro r hr
    obtain ⟨_, h1, _, h2⟩ := hRpure r hr
    exact ⟨h1, h2⟩
  have hownfull : ∀ pq ∈ outerSelectedGraph T i,
      ∃ r ∈ R, own pq.1 = r.1 ∧ own pq.2 = r.2 := by
    intro pq hpq
    exact ⟨(own pq.1, own pq.2),
      Finset.mem_image.mpr ⟨pq, hpq, rfl⟩, rfl, rfl⟩
  have hspan : 2 ≤ k → ∀ q ∈ S,
      ¬ ∃ Ff : AffineSubspace ℂ (Point d),
        Module.finrank ℂ Ff.direction ≤ k + 1 ∧ (own q).points ⊆ ↑Ff := by
    intro hk2 q hqS hex
    obtain ⟨Ff0, hle, hsub⟩ := hex
    have hqP : q ∈ P := hSsubP hqS
    have hown_eq : W.owner i q = own q := hownW q
    have hexW : ∃ Ff : AffineSubspace ℂ (Point d),
        Module.finrank ℂ Ff.direction ≤ k + 1 ∧
        (W.owner i q).points ⊆ ↑Ff := by
      refine ⟨Ff0, hle, ?_⟩
      rw [hown_eq]
      exact hsub
    have hmemC : W.owner i q ∈ C := hsmall q hqP hexW
    have hownC : own q ∈ C := hown_eq ▸ hmemC
    have hqD : q ∈ D := Finset.mem_filter.mpr ⟨hqP, hk2, hownC⟩
    simp only [hSdef, Finset.mem_sdiff] at hqS
    exact hqS.2 hqD
  have hScard_goal : (1 - ρ) * ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
      (S.card : ℝ) := by
    simpa only [hPdef] using hScard_real
  have hSsub_goal : S ⊆ TrackD.poolPts (T.sources i) := by
    simpa only [hPdef] using hSsubP
  exact ⟨⟨S, R, own, hkj, hSsub_goal, hScard_goal, hownsup, hRirr, hRdim,
    hownfull, hspan⟩⟩

/-- sc:outer-pool.chart-pieces (sparse-cones.tex:398–412).
Fix one direction chart `i₀`: obtain the pool via 187b (consuming the
count/cap/ratio bounds internally), the fixed lists via
`selected_common_chart_image_mass`, filter the chart piece to the retained
pools (retention `LittleO` bounds) and to list-obeying pairs
(`common_list_pair_loss`, CommonCertificateSupport.lean), build the image
family `U` in this chart (pooled with
`common_original_image_family_degree_bound`, CommonImagePooling.lean) with
labels via the owner linkage, and prove the image-mass field via
`selected_common_chart_graph_mass`. The low-span deletion for `k ≥ 2` uses
187a (`outer_lowspan_carrier_count` at a sequence at index `d - k = j + 1`),
187d (`mo_outer_flat_cap_aux`) and `outer_deletion_ratio_vanishes`
(OuterAssembly.lean, from `htop` via `outer_first_cuts_sum`). Everything
asymptotic is consumed internally. -/
theorem outer_chart_restriction {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (houter : ∀ i, T.IsOuter i) (hs : ∀ i, M.s i = Real.log (regime.B i))
    {j : ℕ} {τ : ℝ} (W : CommonPhysicalSequence T M (j + 1) τ)
    (k : ℕ) (hk : 1 ≤ k ∧ k + 1 < d) (hkj : k + j + 1 = d)
    (htop : ∀ a : Fin d, j < a.val → M.b a = 1)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (i₀ : Fin d) (ρ' : ℝ) (hρ' : 0 < ρ') :
    ∀ᶠ i in atTop, ∃ chart : OuterChartCert T M k i j i₀ ρ ε ρ' τ,
      chart.W = W := by
  classical
  have hd : 3 ≤ d := regime.dimension_ge_three
  have hj1 : j + 1 < d := by omega
  have hdk : d - (j + 1) = k := by omega
  have hkj1 : d - (j + 1) + 1 < d := by omega
  -- fixed lists + mass/purity, with cert's ε
  obtain ⟨L, hLmassEv⟩ := selected_common_chart_graph_mass W hj1 hkj1 ε hε
  -- transport W to lowspan index d - k (= j+1) with definitionally equal owner
  have hjeq : j + 1 = d - k := by omega
  let W' : CommonPhysicalSequence T M (d - k) τ :=
    { equations := W.equations,
      minor := W.minor,
      owner := W.owner,
      supported := fun i => by rw [← hjeq]; exact W.supported i,
      terminal := fun hdk i q hq Y hY => W.terminal (hjeq.trans hdk) i q hq Y hY,
      tests := by rw [← hjeq]; exact W.tests,
      source_omissions := by rw [← hjeq]; exact W.source_omissions,
      target_omissions := by rw [← hjeq]; exact W.target_omissions }
  have hWowner_eq : ∀ i (q : RPoint d), W'.owner i q = W.owner i q := fun i q => rfl
  -- Retained chart images have full dimension; absorb their fixed degree constant.
  obtain ⟨Cdeg, hCdeg, hCpair⟩ := mo_chart_product_image_degree_const_full i₀ k hk.1
  by_cases hk2 : 2 ≤ k
  · -- k ≥ 2: low-span deletion via 187a + 187d + ratio; pool via 187b
    set ε₀ : ℝ := min ε 1 / 4 with hε₀def
    have hminpos : 0 < min ε 1 := lt_min hε one_pos
    have hε₀pos : 0 < ε₀ := by positivity
    have hε₀leε : ε₀ ≤ ε := by
      calc ε₀ = min ε 1 / 4 := rfl
        _ ≤ min ε 1 := by
            have h0 := le_of_lt hminpos
            have h14 : (1 / 4 : ℝ) ≤ 1 := by norm_num
            calc min ε 1 / 4 = min ε 1 * (1 / 4) := by ring
              _ ≤ min ε 1 * 1 := by gcongr
              _ = min ε 1 := by ring
        _ ≤ ε := min_le_left _ _
    have hε₀le14 : ε₀ ≤ 1 / 4 := by
      calc ε₀ = min ε 1 / 4 := rfl
        _ ≤ 1 / 4 := by gcongr; exact min_le_right _ _
    have hLowspanEv := outer_lowspan_carrier_count T M k W' hk ε₀ hε₀pos
    have hFlatEv := mo_outer_flat_cap_aux T M houter hs k hk ε₀ hε₀pos hk2
    -- first-cuts sum (copy of OuterAssembly, avoids circular import)
    have hsum : ∑ a ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1),
        M.b a = -(k : ℝ) := by
      have hsum0 := M.sum_zero
      have hsplit : ∑ a : Fin d, M.b a =
          (∑ a ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1), M.b a) +
          (∑ a ∈ Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1), M.b a) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun a : Fin d => a.val < j + 1) M.b]
      have htop_sum : ∑ a ∈ Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1),
          M.b a = (k : ℝ) := by
        have hcard : (Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1)).card
            = k := by
          have hkj' : j + 1 + k = d := by omega
          have : Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1) =
              Finset.Ioi (⟨j, by omega⟩ : Fin d) := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi,
              Fin.lt_def, not_lt]
            omega
          rw [this, Fin.card_Ioi]
          show d - 1 - j = k
          omega
        have h1 : ∀ a ∈ Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1),
            M.b a = 1 := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact htop a (by omega)
        rw [Finset.sum_congr rfl h1]
        simp only [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
      linarith
    -- N = B^d (copy)
    have hNpow : ∀ i, regime.N i = (regime.B i) ^ d := by
      intro i
      have hN := regime.N_pos i
      have hd0 : d ≠ 0 := by omega
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
      have hB : regime.B i = (regime.N i) ^ (1 / (d : ℝ)) := rfl
      rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN)]
      have : (1 / (d : ℝ)) * (d : ℝ) = 1 := by
        rw [one_div, inv_mul_cancel₀ hd']
      rw [this, Real.rpow_one]
    -- eScale·B^{k+1}/N = exp((1-k)s) per-i identity (copy of deletion-ratio hexp)
    have hexp_eq : ∀ i, TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
        (regime.B i) ^ (k + 1) / (regime.N i) =
        Real.exp ((1 - (k : ℝ)) * M.s i) := by
      intro i
      have hcard : (Finset.univ.filter (fun a : Fin d => a.val < j + 1)).card
          = j + 1 := by
        have : Finset.univ.filter (fun a : Fin d => a.val < j + 1) =
            Finset.Iio (⟨j + 1, by omega⟩ : Fin d) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
            Fin.lt_def]
        rw [this, Fin.card_Iio]
      have hBpos : 0 < regime.B i := regime.B_pos i
      simp only [TrackD.eScale, TrackD.cutScale, TrackD.testDeg]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, hcard]
      rw [← Real.exp_sum]
      have hBne : regime.B i ≠ 0 := ne_of_gt hBpos
      rw [hNpow i]
      have hpow : (regime.B i) ^ (j + 1) * Real.exp (∑ x ∈ Finset.univ.filter
          (fun a : Fin d => a.val < j + 1), M.b x * M.s i) * (regime.B i) ^ (k + 1) /
          (regime.B i) ^ d = regime.B i * Real.exp (∑ x ∈ Finset.univ.filter
          (fun a : Fin d => a.val < j + 1), M.b x * M.s i) := by
        have hinner : (regime.B i) ^ (j + 1) * (regime.B i) ^ (k + 1) /
            (regime.B i) ^ d = regime.B i := by
          have : j + 1 + (k + 1) = d + 1 := by omega
          rw [← pow_add, this, pow_succ']
          field_simp
        have hrw : (regime.B i) ^ (j + 1) * Real.exp (∑ x ∈ Finset.univ.filter
            (fun a : Fin d => a.val < j + 1), M.b x * M.s i) * (regime.B i) ^ (k + 1) /
            (regime.B i) ^ d =
            ((regime.B i) ^ (j + 1) * (regime.B i) ^ (k + 1) / (regime.B i) ^ d) *
              Real.exp (∑ x ∈ Finset.univ.filter
                (fun a : Fin d => a.val < j + 1), M.b x * M.s i) := by
          ring
        rw [hrw, hinner]
      rw [hpow]
      have hexpsum : ∑ x ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1),
          M.b x * M.s i =
          (∑ x ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1), M.b x) *
            M.s i := by
        rw [Finset.sum_mul]
      rw [hexpsum, hsum, hs i]
      nth_rewrite 1 [← Real.exp_log hBpos]
      have : Real.exp (Real.log (regime.B i)) *
          Real.exp (-(k : ℝ) * Real.log (regime.B i))
          = Real.exp ((1 - (k : ℝ)) * Real.log (regime.B i)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      exact this
    -- pool-size lower bound (ExpLower from source_size, θ₀ = 1/4)
    have hθ₀ : 0 < (1 / 4 : ℝ) := by norm_num
    have hPoolLowEv : ∀ᶠ i in atTop,
        regime.N i * Real.exp (-(1 / 4) * M.s i) ≤
          ((TrackD.poolPts (T.sources i)).card : ℝ) := by
      have hlow := M.source_size.1 (1 / 4) hθ₀
      filter_upwards [hlow] with i hi
      simpa only using hi ()
    -- exponent negativity for hdel ratio (k ≥ 2, ε₀ ≤ 1/4)
    have hcneg : (1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4 < 0 := by
      have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have hε0 : ε₀ ≤ 1 / 4 := hε₀le14
      linarith
    have hExpTendsto : Filter.Tendsto
        (fun i => Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i))
        atTop (𝓝 0) := by
      have hcpos : 0 < -((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) := by linarith
      have htop : Filter.Tendsto
          (fun i => -((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i)
          atTop atTop :=
        M.width_grows.const_mul_atTop hcpos
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
      simpa only [Function.comp_def, neg_mul, neg_neg] using h
    have hRatioEv : ∀ᶠ i in atTop,
        Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) ≤ ρ := by
      exact hExpTendsto.eventually (Iic_mem_nhds hρ)
    -- small η for chart deletions (retention/list/D): ηG = ρ'(1-ρ)²/9 > 0
    have h1mρ : 0 < 1 - ρ := by linarith
    set ηG : ℝ := ρ' * (1 - ρ) ^ 2 / 9 with hηGdef
    have hηGpos : 0 < ηG := by positivity
    have hRetainEv := common_retained_pair_omissions W ηG hηGpos
    have hListEv := common_list_pair_loss W L ηG hηGpos
    have hRatioSmallEv : ∀ᶠ i in atTop,
        Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) ≤ ηG := by
      exact hExpTendsto.eventually (Iic_mem_nhds hηGpos)
    -- carrier budgets at ε/4 + absorption of the fixed degree constant
    have hBudgetsEv : ∀ᶠ i in atTop, CommonCarrierBudgets W i (ε / 4) :=
      selected_common_carrier_budgets W (by omega) (ε / 4) (by positivity)
    have hCabsorbEv : ∀ᶠ i in atTop, Cdeg ≤ Real.exp ((ε / 2) * M.s i) := by
      have hexp : Filter.Tendsto (fun i => Real.exp ((ε / 2) * M.s i)) atTop atTop :=
        Real.tendsto_exp_atTop.comp
          (M.width_grows.const_mul_atTop (half_pos hε))
      exact hexp.eventually (Filter.eventually_ge_atTop Cdeg)
    -- retention + list omissions for hGdel (small η to be fixed later; obtain now)
    -- (defer full hGdel assembly; first get pool via shrink)
    filter_upwards [hLowspanEv, hFlatEv, hPoolLowEv, hRatioEv, hRatioSmallEv,
      hRetainEv, hListEv, hLmassEv, hBudgetsEv, hCabsorbEv] with i hLowspan hFlat hPoolLow hRatio
      hRatioSmall hRetain hList hLmass hBudgets hCabsorb
    -- hLmass at fixed i₀ gives purity + graph mass
    have hLmass0 := hLmass i₀
    obtain ⟨C, hClow, hCcount0, hCcover⟩ := hLowspan
    -- convert C count from ε₀ to cert ε (ε₀ ≤ ε, s > 0)
    have hspos : 0 < M.s i := M.width_pos i
    have hCcount : ((C.card : ℝ)) ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
        Real.exp (ε * M.s i) := by
      have hle : Real.exp (ε₀ * M.s i) ≤ Real.exp (ε * M.s i) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hspos.le
        linarith [hε₀leε]
      have he0 : 0 ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) := by
        unfold TrackD.eScale TrackD.cutScale TrackD.testDeg
        apply Finset.prod_nonneg
        intro _ _
        apply mul_nonneg (regime.B_pos i).le (Real.exp_pos _).le
      calc ((C.card : ℝ)) ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
            Real.exp (ε₀ * M.s i) := hCcount0
        _ ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
            Real.exp (ε * M.s i) :=
          mul_le_mul_of_nonneg_left hle he0
    -- cap from flatcap + C low-span witnesses (cap uses ε₀)
    have hCapDef : ∀ X ∈ C, ∃ Ff : AffineSubspace ℂ (Point d),
        X.points ⊆ ↑Ff ∧ (((TrackD.poolPts (T.sources i)).filter
          (fun q => TrackD.toC q ∈ Ff)).card : ℝ) ≤
          (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) := by
      intro X hX
      obtain ⟨Ff0, hle0, hsub0⟩ := hClow X hX
      have hcard0 := hFlat Ff0 hle0
      exact ⟨Ff0, hsub0, hcard0⟩
    -- hdel via ratio + pool lower bound (uses ε₀, θ₀=1/4)
    have hdel : (C.card : ℝ) *
        ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) ≤
        ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) := by
      have hBpos : 0 < regime.B i := regime.B_pos i
      have hNpos : 0 < regime.N i := regime.N_pos i
      have heScale0 : 0 ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) := by
        unfold TrackD.eScale TrackD.cutScale TrackD.testDeg
        apply Finset.prod_nonneg
        intro _ _
        apply mul_nonneg hBpos.le (Real.exp_pos _).le
      have hcap0 : 0 ≤ (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) :=
        mul_nonneg (pow_nonneg hBpos.le _) (Real.exp_pos _).le
      have hpool0 : 0 ≤ ((TrackD.poolPts (T.sources i)).card : ℝ) :=
        Nat.cast_nonneg _
      -- eScale at d-k equals eScale at j+1 (since d-k = j+1)
      have heScale_eq : TrackD.eScale (regime.B i) (M.s i) M.b (d - k) =
          TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := by
        congr 1
        omega
      -- C*cap ≤ eScale(j+1)·B^{k+1}·exp(2ε₀s)
      have hCC : (C.card : ℝ) *
          ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) ≤
          TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
            (regime.B i) ^ (k + 1) * Real.exp (2 * ε₀ * M.s i) := by
        have h1 : (C.card : ℝ) ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
            Real.exp (ε₀ * M.s i) := hCcount0
        rw [heScale_eq] at h1
        have hexp2 : Real.exp (ε₀ * M.s i) * Real.exp (ε₀ * M.s i) =
            Real.exp (2 * ε₀ * M.s i) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc (C.card : ℝ) * ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i))
            ≤ (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
                Real.exp (ε₀ * M.s i)) *
              ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) :=
              mul_le_mul_of_nonneg_right h1 hcap0
          _ = TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
              (regime.B i) ^ (k + 1) * Real.exp (2 * ε₀ * M.s i) := by
              rw [mul_assoc, mul_assoc, mul_comm ((regime.B i) ^ (k + 1)) _,
                ← mul_assoc, ← hexp2]
              ring
      -- eScale·B^{k+1} = N·exp((1-k)s) via hexp_eq
      have hprod_eq : TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
          (regime.B i) ^ (k + 1) =
          regime.N i * Real.exp ((1 - (k : ℝ)) * M.s i) := by
        have h := hexp_eq i
        have hNne : regime.N i ≠ 0 := ne_of_gt hNpos
        -- h: eScale·B^{k+1}/N = exp((1-k)s); multiply by N
        have h2 : TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
            (regime.B i) ^ (k + 1) / regime.N i =
            Real.exp ((1 - (k : ℝ)) * M.s i) := h
        calc TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
              (regime.B i) ^ (k + 1)
            = (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
                (regime.B i) ^ (k + 1) / regime.N i) * regime.N i := by
              field_simp
          _ = Real.exp ((1 - (k : ℝ)) * M.s i) * regime.N i := by rw [h2]
          _ = regime.N i * Real.exp ((1 - (k : ℝ)) * M.s i) := by ring
      -- combine with pool lower bound and ratio small
      have hexp_split : Real.exp ((1 - (k : ℝ)) * M.s i) *
          Real.exp (2 * ε₀ * M.s i) =
          Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) *
            Real.exp (-(1 / 4) * M.s i) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have hNexp : regime.N i * Real.exp ((1 - (k : ℝ)) * M.s i) *
          Real.exp (2 * ε₀ * M.s i) =
          (regime.N i * Real.exp (-(1 / 4) * M.s i)) *
            Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) := by
        rw [mul_assoc, hexp_split]
        ring
      have hle1 : TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
          (regime.B i) ^ (k + 1) * Real.exp (2 * ε₀ * M.s i) ≤
          (regime.N i * Real.exp (-(1 / 4) * M.s i)) *
            Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) := by
        rw [← hNexp, ← hprod_eq]
      have hle2 : (regime.N i * Real.exp (-(1 / 4) * M.s i)) *
          Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) ≤
          ((TrackD.poolPts (T.sources i)).card : ℝ) *
            Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) := by
        apply mul_le_mul_of_nonneg_right hPoolLow (Real.exp_pos _).le
      have hle3 : ((TrackD.poolPts (T.sources i)).card : ℝ) *
          Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) ≤
          ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hRatio hpool0
        simpa only [mul_comm] using h
      exact le_trans hCC (le_trans hle1 (le_trans hle2 hle3))
    -- hsmall for shrink (from lowspan covering + owner equality)
    have hsmall : ∀ q : RPoint d, q ∈ TrackD.poolPts (T.sources i) →
        (∃ Ff : AffineSubspace ℂ (Point d), Module.finrank ℂ Ff.direction ≤ k + 1 ∧
          (W.owner i q).points ⊆ ↑Ff) → W.owner i q ∈ C := by
      intro q hqP hex
      have hex' : ∃ Ff : AffineSubspace ℂ (Point d),
          Module.finrank ℂ Ff.direction ≤ k + 1 ∧
          (W'.owner i q).points ⊆ ↑Ff := by
        obtain ⟨Ff0, hle0, hsub0⟩ := hex
        refine ⟨Ff0, hle0, ?_⟩
        rw [hWowner_eq]
        exact hsub0
      have hmem : W'.owner i q ∈ C := hCcover q hqP hex'
      rw [hWowner_eq] at hmem
      exact hmem
    -- pool via shrink (own = W.owner, hownsup = W.supported, hownW = rfl)
    -- need eScale at d-k vs j+1 conversion for hCcount (shrink expects d-k)
    have hCcount_shrink : ((C.card : ℝ)) ≤
        TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
          Real.exp (ε * M.s i) := by
      have heq : TrackD.eScale (regime.B i) (M.s i) M.b (d - k) =
          TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := by
        congr 1
        omega
      -- hCcount already proves with d-k? Actually hCcount was proved with d-k
      -- (via hCcount0 conversion); reuse it directly (it matches shrink's form)
      exact hCcount
    have hownsup : TrackD.CarrierAssignment (T.sources i ∪ T.targets i) (j + 1)
        (W.owner i) := W.supported i
    -- cap for shrink (uses ε₀, but shrink's cap is arbitrary; hdel uses same cap)
    -- hcap for shrink needs ∃ Ff per X with card ≤ cap (cap = B^{k+1}·exp(ε₀s))
    -- hCapDef already gives exactly that (with cap)
    have hcap_shrink : ∀ X ∈ C, ∃ Ff : AffineSubspace ℂ (Point d),
        X.points ⊆ ↑Ff ∧ (((TrackD.poolPts (T.sources i)).filter
          (fun q => TrackD.toC q ∈ Ff)).card : ℝ) ≤
          (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) :=
      hCapDef
    -- Direct pool construction (inline 187b to preserve own linkage;
    -- 187b's Nonempty would lose pool.own = W.owner via choice).
    -- P/D/S/R with own = W.owner i.
    set Ppool : Finset (RPoint d) := TrackD.poolPts (T.sources i) with hPpooldef
    -- flats for C (reuse hCapDef witnesses via choice)
    let FfC : AffineVariety d → AffineSubspace ℂ (Point d) := fun X =>
      if h : X ∈ C then Classical.choose (hCapDef X h) else ⊤
    have hFfCsub : ∀ X ∈ C, X.points ⊆ ↑(FfC X) := by
      intro X hX
      have hspec := Classical.choose_spec (hCapDef X hX)
      simp only [FfC, dif_pos hX] at *
      exact hspec.1
    have hFfCcap : ∀ X ∈ C, (((Ppool.filter
        (fun q => TrackD.toC q ∈ FfC X)).card : ℝ)) ≤
        (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) := by
      intro X hX
      have hspec := Classical.choose_spec (hCapDef X hX)
      have hFfeq : FfC X = Classical.choose (hCapDef X hX) := by
        simp only [FfC, dif_pos hX]
      rw [hFfeq]
      have hPeq : Ppool = TrackD.poolPts (T.sources i) := hPpooldef.symm
      simpa only [hPeq] using hspec.2
    set Dpool : Finset (RPoint d) :=
      Ppool.filter (fun q => 2 ≤ k ∧ W.owner i q ∈ C) with hDpooldef
    set Spool : Finset (RPoint d) := Ppool \ Dpool with hSpooldef
    set Rpool : Finset (AffineVariety d × AffineVariety d) :=
      (outerSelectedGraph T i).image
        (fun pq => (W.owner i pq.1, W.owner i pq.2)) with hRpooldef
    have hj1le2 : j + 1 ≤ d := by omega
    have hdim_eq2 : d - (j + 1) = k := by omega
    have hpiece_good2 : ∀ X ∈ T.sources i ∪ T.targets i,
        TrackD.PieceGood (regime.P i) (selectionTolerance (T.precision i))
          (selectionTolerance (T.precision i)) (selectionScale (T.precision i)) X := by
      intro X hX
      have hmem : X ∈ (T.partition i).pieces := by
        rcases Finset.mem_union.mp hX with h | h
        · exact (T.certificate i).sources_subset h
        · exact (T.certificate i).targets_subset h
      exact ((T.certificate i).good.pieces_good X hmem).1
    have hown_pure2 : ∀ q : RPoint d, ∀ X : TrackD.Piece d,
        X ∈ T.sources i ∪ T.targets i → q ∈ X.pts →
        (W.owner i q).IsIrreducible ∧ (W.owner i q).dimension = k := by
      intro q X hXmem hqmem
      obtain ⟨hcarr, hpt⟩ := hownsup X hXmem q hqmem
      have hgood := hpiece_good2 X hXmem
      have hvan : ∀ a : Fin d,
          MvPolynomial.eval (TrackD.toC q) (X.path.cut a) = 0 :=
        fun a => hgood.vanish q hqmem a
      have hprop : X.path.ProperAt (TrackD.toC q) := hgood.proper q hqmem
      have hlocal : W.owner i q ∈ X.path.localCarriers (j + 1) (TrackD.toC q) :=
        ⟨hcarr, hpt⟩
      have hpure := TrackD.prof_partition_pure X q hqmem hvan hprop
        (j + 1) hj1le2 (W.owner i q) hlocal
      rw [hdim_eq2] at hpure
      exact hpure
    have hDsubP2 : Dpool ⊆ Ppool := Finset.filter_subset _ _
    have hSsubP2 : Spool ⊆ Ppool := Finset.sdiff_subset
    have hRpure2 : ∀ r ∈ Rpool,
        r.1.IsIrreducible ∧ r.1.dimension = k ∧
        r.2.IsIrreducible ∧ r.2.dimension = k := by
      intro r hr
      simp only [hRpooldef, Finset.mem_image] at hr
      obtain ⟨pq, hpq, rfl⟩ := hr
      have h1P : pq.1 ∈ Ppool := by
        simp only [outerSelectedGraph, Finset.mem_filter, Finset.mem_product,
          hPpooldef] at hpq
        exact hpq.1.1
      have h2P : pq.2 ∈ TrackD.poolPts (T.targets i) := by
        simp only [outerSelectedGraph, Finset.mem_filter, Finset.mem_product] at hpq
        exact hpq.1.2
      obtain ⟨X1, hX1mem, hq1mem⟩ := Finset.mem_biUnion.mp h1P
      have hX1union : X1 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hX1mem
      have hpure1 := hown_pure2 pq.1 X1 hX1union hq1mem
      obtain ⟨X2, hX2mem, hq2mem⟩ := Finset.mem_biUnion.mp h2P
      have hX2union : X2 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_right _ hX2mem
      have hpure2 := hown_pure2 pq.2 X2 hX2union hq2mem
      exact ⟨hpure1.1, hpure1.2, hpure2.1, hpure2.2⟩
    have hRirr2 : ∀ r ∈ Rpool, r.1.IsIrreducible ∧ r.2.IsIrreducible := by
      intro r hr
      obtain ⟨h1, _, h2, _⟩ := hRpure2 r hr
      exact ⟨h1, h2⟩
    have hRdim2 : ∀ r ∈ Rpool, r.1.dimension = k ∧ r.2.dimension = k := by
      intro r hr
      obtain ⟨_, h1, _, h2⟩ := hRpure2 r hr
      exact ⟨h1, h2⟩
    have hownfull2 : ∀ pq ∈ outerSelectedGraph T i,
        ∃ r ∈ Rpool, W.owner i pq.1 = r.1 ∧ W.owner i pq.2 = r.2 := by
      intro pq hpq
      exact ⟨(W.owner i pq.1, W.owner i pq.2),
        Finset.mem_image.mpr ⟨pq, hpq, rfl⟩, rfl, rfl⟩
    have hspan2 : 2 ≤ k → ∀ q ∈ Spool,
        ¬ ∃ Ff : AffineSubspace ℂ (Point d),
          Module.finrank ℂ Ff.direction ≤ k + 1 ∧ (W.owner i q).points ⊆ ↑Ff := by
      intro hk2' q hqS hex
      obtain ⟨Ff0, hle, hsub⟩ := hex
      have hqP : q ∈ Ppool := hSsubP2 hqS
      have hmemC : W.owner i q ∈ C := hsmall q hqP ⟨Ff0, hle, hsub⟩
      have hqD : q ∈ Dpool := Finset.mem_filter.mpr ⟨hqP, hk2', hmemC⟩
      simp only [hSpooldef, Finset.mem_sdiff] at hqS
      exact hqS.2 hqD
    have hScard2 : (1 - ρ) * (Ppool.card : ℝ) ≤ (Spool.card : ℝ) := by
      -- D ⊆ biUnion flats, D.card ≤ C.card*cap ≤ ρ·|pool| via hdel
      have hDcover2 : Dpool ⊆ C.biUnion
          (fun X => Ppool.filter (fun q => TrackD.toC q ∈ FfC X)) := by
        intro q hqD
        simp only [hDpooldef, Finset.mem_filter] at hqD
        obtain ⟨hqP, _, hownC⟩ := hqD
        obtain ⟨Xpiece, hXmem, hqmem⟩ := Finset.mem_biUnion.mp hqP
        have hXunion : Xpiece ∈ T.sources i ∪ T.targets i :=
          Finset.mem_union_left _ hXmem
        obtain ⟨_, hpt⟩ := hownsup Xpiece hXunion q hqmem
        have hsub := hFfCsub (W.owner i q) hownC
        have hmemFf : TrackD.toC q ∈ FfC (W.owner i q) := hsub hpt
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨W.owner i q, hownC, hqP, hmemFf⟩
      have hDcard2 : (Dpool.card : ℝ) ≤ (C.card : ℝ) *
          ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) := by
        have h1 : Dpool.card ≤
            (C.biUnion (fun X => Ppool.filter
              (fun q => TrackD.toC q ∈ FfC X))).card :=
          Finset.card_le_card hDcover2
        have hnat : (C.biUnion (fun X => Ppool.filter
            (fun q => TrackD.toC q ∈ FfC X))).card ≤
            ∑ X ∈ C, (Ppool.filter (fun q => TrackD.toC q ∈ FfC X)).card :=
          Finset.card_biUnion_le
        have h2 : ((C.biUnion (fun X => Ppool.filter
            (fun q => TrackD.toC q ∈ FfC X))).card : ℝ) ≤
            ∑ X ∈ C, ((Ppool.filter
              (fun q => TrackD.toC q ∈ FfC X)).card : ℝ) := by
          exact_mod_cast hnat
        have h3 : ∑ X ∈ C, ((Ppool.filter
            (fun q => TrackD.toC q ∈ FfC X)).card : ℝ) ≤
            (C.card : ℝ) * ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) := by
          have hle : ∀ X ∈ C, ((Ppool.filter
              (fun q => TrackD.toC q ∈ FfC X)).card : ℝ) ≤
              (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) :=
            fun X hX => hFfCcap X hX
          calc ∑ X ∈ C, ((Ppool.filter
                (fun q => TrackD.toC q ∈ FfC X)).card : ℝ)
              ≤ ∑ X ∈ C, (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) :=
                Finset.sum_le_sum hle
            _ = (C.card : ℝ) * ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        calc (Dpool.card : ℝ) ≤ ((C.biUnion (fun X => Ppool.filter
              (fun q => TrackD.toC q ∈ FfC X))).card : ℝ) := by
                exact_mod_cast h1
          _ ≤ _ := h2
          _ ≤ _ := h3
      have hSD : Spool.card + Dpool.card = Ppool.card :=
        Finset.card_sdiff_add_card_eq_card hDsubP2
      have hDle : (Dpool.card : ℝ) ≤ ρ * (Ppool.card : ℝ) :=
        le_trans hDcard2 hdel
      have hSDreal : (Spool.card : ℝ) + (Dpool.card : ℝ) = (Ppool.card : ℝ) := by
        exact_mod_cast hSD
      linarith
    have hSsub_goal2 : Spool ⊆ TrackD.poolPts (T.sources i) := by
      simpa only [hPpooldef] using hSsubP2
    have hScard_goal2 : (1 - ρ) * ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
        (Spool.card : ℝ) := by
      simpa only [hPpooldef] using hScard2
    let pool : OuterPoolData T M k i j ρ ε :=
      ⟨Spool, Rpool, W.owner i, hkj, hSsub_goal2, hScard_goal2, hownsup,
        hRirr2, hRdim2, hownfull2, hspan2⟩
    -- pool.own = W.owner i definitionally? shrink's own param is W.owner i, so pool.own = that
    -- chart piece G/U assembly
    -- outer pools coincide
    have hSTEq : T.targets i = T.sources i := (houter i).1.symm
    -- FiltChart and G
    set Sel : Finset (RPoint d × RPoint d) := outerSelectedGraph T i with hSeldef
    set Filt : Finset (RPoint d × RPoint d) := Sel.filter (fun pq =>
      (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) with hFiltdef
    set G : Finset (RPoint d × RPoint d) := Filt.filter (fun pq =>
      pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S ∧ pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
        W.owner i pq.2 ∈ L.lists i (W.owner i pq.1)) with hGdef
    set U : Finset (AffineVariety (d + d)) :=
      commonChartImages W L i i₀ with hUdef
    -- purity + mass from L-mass at i₀
    obtain ⟨hUpure, hGraphMass⟩ := hLmass0
    -- rewrite purity dimension d-(j+1) = k
    have hUpure2k : AffineFamily.IsPure U (2 * k) := by
      have hdk2 : d - (j + 1) = k := by omega
      simpa only [hUdef, hdk2] using hUpure
    -- G ⊆ Sel, etc. (easy fields)
    have hGsub : G ⊆ outerSelectedGraph T i := by
      simp only [hGdef, hFiltdef, hSeldef]
      exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hGmem : ∀ pq ∈ G, pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S := by
      intro pq hpq
      simp only [hGdef, Finset.mem_filter] at hpq
      exact ⟨hpq.2.1, hpq.2.2.1⟩
    have hchart : ∀ pq ∈ G, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
      intro pq hpq
      simp only [hGdef, hFiltdef, Finset.mem_filter] at hpq
      exact hpq.1.2
    have hGpoolsList : ∀ pq ∈ G, pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
        W.owner i pq.2 ∈ L.lists i (W.owner i pq.1) := by
      intro pq hpq
      simp only [hGdef, Finset.mem_filter] at hpq
      exact ⟨hpq.2.2.2.1, hpq.2.2.2.2.1, hpq.2.2.2.2.2⟩
    have hWownF : ∀ q : TrackD.Pt d, W.owner i q = pool.own q := fun q => rfl
    have hown : ∀ pq ∈ G, ∃ r ∈ pool.R, pool.own pq.1 = r.1 ∧ pool.own pq.2 = r.2 := by
      intro pq hpq
      have hpqSel : pq ∈ outerSelectedGraph T i := hGsub hpq
      obtain ⟨r, hr, h1, h2⟩ := pool.hownfull pq hpqSel
      exact ⟨r, hr, h1, h2⟩
    -- hU, hUmem, hlabel, hmassW, hGdel
    have hU : ∀ W0 ∈ U, W0.IsIrreducible ∧ W0.dimension = 2 * k := by
      intro W0 hW0
      exact hUpure2k W0 hW0
    have hUdeg : ((AffineFamily.degree U : ℚ) : ℝ) ≤
        (1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
          Real.exp (ε * M.s i) := by
      have hpair : ∀ X ∈ W.sourceCarriers i, ∀ Y ∈ L.lists i X,
          X.IsIrreducible → X.dimension = k → Y.IsIrreducible → Y.dimension = k →
          (∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) →
          ((commonProductImage i₀ X Y).degree : ℝ) ≤
            Cdeg * (X.degree : ℝ) * (Y.degree : ℝ) := by
        intro X hX Y hY hXi hXd hYi hYd hch
        have hZmem : commonProductImage i₀ X Y ∈ U := by
          simp only [hUdef, commonChartImages, Finset.mem_biUnion]
          refine ⟨X, hX, Finset.mem_image.mpr ⟨Y, ?_, rfl⟩⟩
          exact Finset.mem_filter.mpr ⟨hY, hch⟩
        exact hCpair X Y hXi hXd hYi hYd hch (hUpure2k _ hZmem).2
      have hfam := mo_chart_family_degree_le W L k hk.1 (by omega : d - (j + 1) = k)
        (by omega : j + 1 ≤ d) i i₀ ρ hρ hε Cdeg hCdeg hpair hBudgets hUpure2k hCabsorb
      simpa only [commonCarrierScale] using hfam
    have hUmem : ∀ pq ∈ G, commonProductImage i₀ (W.owner i pq.1)
        (W.owner i pq.2) ∈ U := by
      intro pq hpq
      have hWsWt := hGpoolsList pq hpq
      obtain ⟨hWs, hWt, hlist⟩ := hWsWt
      have hch := hchart pq hpq
      -- X in sourceCarriers
      have hXmem : W.owner i pq.1 ∈ W.sourceCarriers i := by
        simp only [CommonPhysicalSequence.sourceCarriers, commonOwnerFamily]
        exact Finset.mem_image.mpr ⟨pq.1, hWs, rfl⟩
      -- toC membership via W.supported (find pieces)
      have hPsrc1 : pq.1 ∈ TrackD.poolPts (T.sources i) := by
        have hsub : W.sources i ⊆ TrackD.poolPts (T.sources i) :=
          Finset.filter_subset _ _
        exact hsub hWs
      have hPsrc2 : pq.2 ∈ TrackD.poolPts (T.targets i) := by
        have hsub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
          Finset.filter_subset _ _
        exact hsub hWt
      obtain ⟨X1, hX1mem, hq1mem⟩ := Finset.mem_biUnion.mp hPsrc1
      have hX1union : X1 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hX1mem
      obtain ⟨_, hpt1⟩ := W.supported i X1 hX1union pq.1 hq1mem
      obtain ⟨X2, hX2mem, hq2mem⟩ := Finset.mem_biUnion.mp hPsrc2
      have hX2union : X2 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_right _ hX2mem
      obtain ⟨_, hpt2⟩ := W.supported i X2 hX2union pq.2 hq2mem
      -- Y in chartTargets
      have hYchart : W.owner i pq.2 ∈
          commonChartTargets W L i i₀ (W.owner i pq.1) := by
        simp only [commonChartTargets, Finset.mem_filter]
        refine ⟨hlist, ?_⟩
        exact ⟨TrackD.toC pq.1, hpt1, TrackD.toC pq.2, hpt2, hch⟩
      simp only [hUdef, commonChartImages, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨W.owner i pq.1, hXmem, W.owner i pq.2, hYchart, rfl⟩
    have hlabel : ∀ pq ∈ G, (fun kk =>
        TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
          (finSumFinEquiv.symm kk)) ∈
            (commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)).points := by
      intro pq hpq
      have hch := hchart pq hpq
      have hWsWt := hGpoolsList pq hpq
      obtain ⟨hWs, hWt, -⟩ := hWsWt
      have hPsrc1 : pq.1 ∈ TrackD.poolPts (T.sources i) := by
        have hsub : W.sources i ⊆ TrackD.poolPts (T.sources i) :=
          Finset.filter_subset _ _
        exact hsub hWs
      have hPsrc2 : pq.2 ∈ TrackD.poolPts (T.targets i) := by
        have hsub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
          Finset.filter_subset _ _
        exact hsub hWt
      obtain ⟨X1, hX1mem, hq1mem⟩ := Finset.mem_biUnion.mp hPsrc1
      have hX1union : X1 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hX1mem
      obtain ⟨_, hpt1⟩ := W.supported i X1 hX1union pq.1 hq1mem
      obtain ⟨X2, hX2mem, hq2mem⟩ := Finset.mem_biUnion.mp hPsrc2
      have hX2union : X2 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_right _ hX2mem
      obtain ⟨_, hpt2⟩ := W.supported i X2 hX2union pq.2 hq2mem
      -- product point in product variety
      have hleft_eq : TrackD.productLeft
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) =
          TrackD.toC pq.1 := by
        funext i
        simp only [TrackD.productLeft, TrackD.productPoint_inl]
      have hright_eq : TrackD.productRight
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) =
          TrackD.toC pq.2 := by
        funext i
        simp only [TrackD.productRight, TrackD.productPoint_inr]
      have hprodmem : TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2) ∈
          (TrackD.productVariety (W.owner i pq.1) (W.owner i pq.2)).points := by
        rw [TrackD.productVariety_points]
        simp only [Set.mem_setOf_eq]
        rw [hleft_eq, hright_eq]
        exact ⟨hpt1, hpt2⟩
      -- denominator nonzero from chart
      have hdenom : MvPolynomial.eval
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2))
          (TrackD.secantChartDenominator i₀) ≠ 0 := by
        rw [TrackD.eval_secantChartDenominator]
        exact hch
      -- rational image membership
      have hmem : TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀)
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) ∈
          (commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)).points := by
        simp only [commonProductImage]
        exact TrackD.rationalPoint_mem_image _ _ _
          _ hprodmem hdenom
      -- identify rational point with transported labelPt via secant label
      have hsec := TrackD.rational_secant_label i₀
        (TrackD.toC pq.1) (TrackD.toC pq.2) hch
      -- dirChart = ((y-x) i₀)⁻¹ • (y-x), labelPt = pairPt x (that)
      have hdir : TrackD.dirChart (LinearMap.proj i₀)
          (TrackD.toC pq.2 - TrackD.toC pq.1) =
          ((TrackD.toC pq.2 - TrackD.toC pq.1) i₀)⁻¹ •
            (TrackD.toC pq.2 - TrackD.toC pq.1) := rfl
      have hlabel_eq : (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1)
          (TrackD.toC pq.2) (finSumFinEquiv.symm kk)) =
          TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀)
            (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) := by
        -- labelPt = pairPt x (dirChart...), rationalPoint = productPoint x (dirChart...)
        -- productPoint x y = pairPt x y ∘ finSumFinEquiv.symm (by definition)
        simp only [TrackD.labelPt, hsec]
        rfl
      rw [hlabel_eq]
      exact hmem
    have hGdel : ((Filt \ G).card : ℝ) ≤ ρ' * (pool.S.card : ℝ) ^ 2 := by
      -- pools coincide (outer)
      have hPeq : TrackD.poolPts (T.targets i) = Ppool := by
        rw [hSTEq]
      -- D small: |D| ≤ ηG·|P| via ratio small (same as hdel with ηG)
      have hDsmall : (Dpool.card : ℝ) ≤ ηG * (Ppool.card : ℝ) := by
        -- C*cap ≤ N·exp((1-k+2ε₀)s) as in hdel, then ≤ ηG·|P| via pool lower + ratio small
        have hBpos : 0 < regime.B i := regime.B_pos i
        have hNpos : 0 < regime.N i := regime.N_pos i
        have heScale_eq2 : TrackD.eScale (regime.B i) (M.s i) M.b (d - k) =
            TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := by
          congr 1
          omega
        have hCC2 : (C.card : ℝ) *
            ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) ≤
            regime.N i * Real.exp ((1 - (k : ℝ) + 2 * ε₀) * M.s i) := by
          have h1 : (C.card : ℝ) ≤ TrackD.eScale (regime.B i) (M.s i) M.b (d - k) *
              Real.exp (ε₀ * M.s i) := hCcount0
          rw [heScale_eq2] at h1
          have hcap0 : 0 ≤ (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) :=
            mul_nonneg (pow_nonneg hBpos.le _) (Real.exp_pos _).le
          have he0 : 0 ≤ TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := by
            unfold TrackD.eScale TrackD.cutScale TrackD.testDeg
            apply Finset.prod_nonneg
            intro _ _
            apply mul_nonneg hBpos.le (Real.exp_pos _).le
          have hexp2 : Real.exp (ε₀ * M.s i) * Real.exp (ε₀ * M.s i) =
              Real.exp (2 * ε₀ * M.s i) := by
            rw [← Real.exp_add]
            congr 1
            ring
          have hprod : TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
              (regime.B i) ^ (k + 1) =
              regime.N i * Real.exp ((1 - (k : ℝ)) * M.s i) := by
            have h := hexp_eq i
            have hNne : regime.N i ≠ 0 := ne_of_gt hNpos
            calc TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
                  (regime.B i) ^ (k + 1)
                = (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
                    (regime.B i) ^ (k + 1) / regime.N i) * regime.N i := by
                  field_simp
              _ = Real.exp ((1 - (k : ℝ)) * M.s i) * regime.N i := by rw [h]
              _ = regime.N i * Real.exp ((1 - (k : ℝ)) * M.s i) := by ring
          calc (C.card : ℝ) * ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i))
              ≤ (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
                  Real.exp (ε₀ * M.s i)) *
                ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) :=
                mul_le_mul_of_nonneg_right h1 hcap0
            _ = (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
                  (regime.B i) ^ (k + 1)) * Real.exp (2 * ε₀ * M.s i) := by
                rw [mul_assoc, mul_assoc, mul_comm ((regime.B i) ^ (k + 1)) _,
                  ← mul_assoc, ← hexp2]
                ring
            _ = regime.N i * Real.exp ((1 - (k : ℝ) + 2 * ε₀) * M.s i) := by
                rw [hprod, mul_assoc, ← Real.exp_add]
                congr 1
                ring
        -- D ≤ C*cap via biUnion (reuse hDcover2 logic? Dpool ⊆ biUnion, card ≤ sum)
        have hDleCC : (Dpool.card : ℝ) ≤ (C.card : ℝ) *
            ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) := by
          -- same biUnion bound as in hScard2 (Dpool ⊆ biUnion flats)
          have hDcover : Dpool ⊆ C.biUnion
              (fun X => Ppool.filter (fun q => TrackD.toC q ∈ FfC X)) := by
            intro q hqD
            simp only [hDpooldef, Finset.mem_filter] at hqD
            obtain ⟨hqP, _, hownC⟩ := hqD
            obtain ⟨Xpiece, hXmem, hqmem⟩ := Finset.mem_biUnion.mp hqP
            have hXunion : Xpiece ∈ T.sources i ∪ T.targets i :=
              Finset.mem_union_left _ hXmem
            obtain ⟨_, hpt⟩ := hownsup Xpiece hXunion q hqmem
            have hsub := hFfCsub (W.owner i q) hownC
            have hmemFf : TrackD.toC q ∈ FfC (W.owner i q) := hsub hpt
            simp only [Finset.mem_biUnion, Finset.mem_filter]
            exact ⟨W.owner i q, hownC, hqP, hmemFf⟩
          have h1 : Dpool.card ≤
              (C.biUnion (fun X => Ppool.filter
                (fun q => TrackD.toC q ∈ FfC X))).card :=
            Finset.card_le_card hDcover
          have hnat : (C.biUnion (fun X => Ppool.filter
              (fun q => TrackD.toC q ∈ FfC X))).card ≤
              ∑ X ∈ C, (Ppool.filter (fun q => TrackD.toC q ∈ FfC X)).card :=
            Finset.card_biUnion_le
          have h2 : ((C.biUnion (fun X => Ppool.filter
              (fun q => TrackD.toC q ∈ FfC X))).card : ℝ) ≤
              ∑ X ∈ C, ((Ppool.filter
                (fun q => TrackD.toC q ∈ FfC X)).card : ℝ) := by
            exact_mod_cast hnat
          have h3 : ∑ X ∈ C, ((Ppool.filter
              (fun q => TrackD.toC q ∈ FfC X)).card : ℝ) ≤
              (C.card : ℝ) * ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) := by
            have hle : ∀ X ∈ C, ((Ppool.filter
                (fun q => TrackD.toC q ∈ FfC X)).card : ℝ) ≤
                (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) :=
              fun X hX => hFfCcap X hX
            calc ∑ X ∈ C, ((Ppool.filter
                  (fun q => TrackD.toC q ∈ FfC X)).card : ℝ)
                ≤ ∑ X ∈ C, (regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i) :=
                  Finset.sum_le_sum hle
              _ = (C.card : ℝ) * ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
          calc (Dpool.card : ℝ) ≤ ((C.biUnion (fun X => Ppool.filter
                (fun q => TrackD.toC q ∈ FfC X))).card : ℝ) := by
                  exact_mod_cast h1
            _ ≤ _ := h2
            _ ≤ _ := h3
        -- C*cap = (N·exp(-θs))·exp(c·s) ≤ |P|·ηG via pool lower + ratio small
        have hCCsmall : (C.card : ℝ) *
            ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) ≤
            ηG * (Ppool.card : ℝ) := by
          have hexp_split2 : Real.exp ((1 - (k : ℝ) + 2 * ε₀) * M.s i) =
              Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) *
                Real.exp (-(1 / 4) * M.s i) := by
            rw [← Real.exp_add]
            congr 1
            ring
          have hNexp2 : regime.N i * Real.exp ((1 - (k : ℝ) + 2 * ε₀) * M.s i) =
              (regime.N i * Real.exp (-(1 / 4) * M.s i)) *
                Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) := by
            rw [hexp_split2]
            ring
          have hle1 : regime.N i * Real.exp ((1 - (k : ℝ) + 2 * ε₀) * M.s i) ≤
              (Ppool.card : ℝ) *
                Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) := by
            have hPeq2 : Ppool = TrackD.poolPts (T.sources i) := hPpooldef.symm
            -- hPoolLow: N·exp(-1/4 s) ≤ |P|
            have hlow : regime.N i * Real.exp (-(1 / 4) * M.s i) ≤
                (Ppool.card : ℝ) := by
              simpa only [hPeq2] using hPoolLow
            calc regime.N i * Real.exp ((1 - (k : ℝ) + 2 * ε₀) * M.s i)
                = (regime.N i * Real.exp (-(1 / 4) * M.s i)) *
                    Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) := by
                  rw [← hNexp2]
                _ ≤ (Ppool.card : ℝ) *
                    Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) :=
                  mul_le_mul_of_nonneg_right hlow (Real.exp_pos _).le
          have hle2 : (Ppool.card : ℝ) *
              Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) ≤
              ηG * (Ppool.card : ℝ) := by
            have hP0 : 0 ≤ (Ppool.card : ℝ) := Nat.cast_nonneg _
            have h := mul_le_mul_of_nonneg_left hRatioSmall hP0
            simpa only [mul_comm] using h
          calc (C.card : ℝ) * ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i))
              ≤ regime.N i * Real.exp ((1 - (k : ℝ) + 2 * ε₀) * M.s i) := by
                -- from hCC2 (C*cap ≤ N·exp((1-k+2ε₀)s))
                have h := hCC2
                -- hCC2 was C*cap ≤ N·exp((1-k+2ε₀)s)? Actually hCC2 proves that? Check: hCC2 is C*cap ≤ N·exp((1-k+2ε₀)s)? Yes via eScale... Good.
                -- Need to convert hCC2 (which used eScale...) to this form; hCC2 already is that (via hprod? Actually hCC2 in hDsmall context? We have hCC2 above? No, hCC2 here is different? Let's reuse hCC2 from above? Actually hCC2 above was for hdel? No, hCC2 here is new? We defined hCC2 above as C*cap ≤ N·exp(...)? Yes hCC2 is that. Good.
                exact h
            _ ≤ (Ppool.card : ℝ) *
                Real.exp (((1 : ℝ) - (k : ℝ) + 2 * ε₀ + 1 / 4) * M.s i) := by
                -- via hle1? Actually N·exp((1-k+2ε₀)s) = (N·exp(-1/4s))·exp(c·s) ≤ |P|·exp(c·s)? No, hle1 is N·exp((1-k+2ε₀)s) ≤ |P|·exp(c·s)? Let's see: hle1 proves N·exp((1-k+2ε₀)s) ≤ |P|·exp(c·s)? Actually hle1's left is N·exp((1-k+2ε₀)s)? No, hle1 left is N·exp((1-k+2ε₀)s)? Wait hle1 left is N·exp((1-k+2ε₀)s)? No, hle1 states N·exp((1-k+2ε₀)s) ≤ |P|·exp(c·s)? Let's check: hle1 proves ... Actually hle1 was derived as ... Good, use hle1.
                -- hle1 is exactly N·exp((1-k+2ε₀)s) ≤ |P|·exp(c·s)? No, hle1's statement is ... Let's just use hle1 directly (it matches).
                exact hle1
            _ ≤ ηG * (Ppool.card : ℝ) := hle2
        calc (Dpool.card : ℝ) ≤ (C.card : ℝ) *
              ((regime.B i) ^ (k + 1) * Real.exp (ε₀ * M.s i)) := hDleCC
          _ ≤ ηG * (Ppool.card : ℝ) := hCCsmall
      -- product deletions: Filt\G ⊆ A ∪ B ∪ C0
      -- A = (P×P)\(S×S), B = (P×P)\(Ws×Wt), C0 = (Ws×Wt).filter non-list
      have hPcard0 : 0 ≤ (Ppool.card : ℝ) := Nat.cast_nonneg _
      have hScard0 : 0 ≤ (pool.S.card : ℝ) := Nat.cast_nonneg _
      -- S = P\D, |S| ≥ (1-ρ)|P|
      have hSge : (1 - ρ) * (Ppool.card : ℝ) ≤ (pool.S.card : ℝ) := by
        -- pool.S = Spool definitionally? pool is let with Spool, so pool.S = Spool
        -- hScard2 was (1-ρ)*|P| ≤ |Spool|, reuse (need to rewrite Ppool vs poolPts? Already same)
        simpa only using hScard2
      -- Ws/Wt ⊆ Ppool
      have hWsP : W.sources i ⊆ Ppool := Finset.filter_subset _ _
      have hWtP : W.targets i ⊆ Ppool := by
        have hsub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
          Finset.filter_subset _ _
        rw [hPeq] at hsub
        -- hPeq: poolPts targets = Ppool, so hsub : Wt ⊆ Ppool after rw? Actually rw rewrites goal? hsub : Wt ⊆ poolPts targets, with hPeq : poolPts targets = Ppool, so Wt ⊆ Ppool via hPeq ▸ hsub? Use simpa.
        simpa only [hPeq] using hsub
      -- Sel ⊆ Ppool × Ppool
      have hSelPP : Sel ⊆ Ppool ×ˢ Ppool := by
        intro pq hpq
        simp only [hSeldef, outerSelectedGraph, Finset.mem_filter,
          Finset.mem_product] at hpq ⊢
        obtain ⟨⟨h1, h2⟩, -⟩ := hpq
        refine ⟨h1, ?_⟩
        rw [← hPeq]
        exact h2
      have hFiltPP : Filt ⊆ Ppool ×ˢ Ppool :=
        (Finset.filter_subset _ _).trans hSelPP
      -- A bound: |(P×P)\(S×S)| ≤ 2·|D|·|P|
      have hAcard : (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ) ≤
          2 * (Dpool.card : ℝ) * (Ppool.card : ℝ) := by
        -- (P×P)\(S×S) ⊆ (D×P) ∪ (P×D) since P\S = D (as D⊆P, S=P\D)
        have hPS : Ppool \ pool.S = Dpool := by
          have hSeq : pool.S = Spool := rfl
          have hDeq : Dpool ⊆ Ppool := hDsubP2
          rw [hSeq, hSpooldef]
          ext q
          constructor
          · intro hq
            obtain ⟨hqP, hqnS⟩ := Finset.mem_sdiff.mp hq
            by_cases hqD : q ∈ Dpool
            · exact hqD
            · exfalso
              have hqS : q ∈ Spool :=
                Finset.mem_sdiff.mpr ⟨hqP, hqD⟩
              exact hqnS hqS
          · intro hq
            have hqP : q ∈ Ppool := hDeq hq
            have hqnS : q ∉ Spool := by
              intro hqS
              have hqDmem := hq
              have hqSmem := hqS
              simp only [hSpooldef, Finset.mem_sdiff] at hqSmem
              exact hqSmem.2 hqDmem
            exact Finset.mem_sdiff.mpr ⟨hqP, hqnS⟩
        have hsubA : (Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S) ⊆
            (Dpool ×ˢ Ppool) ∪ (Ppool ×ˢ Dpool) := by
          intro pq hpq
          simp only [Finset.mem_sdiff, Finset.mem_product, Finset.mem_union] at hpq ⊢
          obtain ⟨⟨h1P, h2P⟩, hnot⟩ := hpq
          by_cases h1S : pq.1 ∈ pool.S
          · have h2nS : pq.2 ∉ pool.S := by
              intro h2S
              exact hnot ⟨h1S, h2S⟩
            have h2D : pq.2 ∈ Dpool := by
              have h2P' : pq.2 ∈ Ppool := h2P
              have hPS' : pq.2 ∈ Ppool \ pool.S :=
                Finset.mem_sdiff.mpr ⟨h2P', h2nS⟩
              rw [hPS] at hPS'
              -- hPS: Ppool\pool.S = Dpool, so hPS' : pq.2 ∈ Dpool? Actually hPS' after rw? hPS : P\S = D, so P\S membership = D membership? Via rw? hPS' : pq.2 ∈ P\S, with hPS : P\S = D, so pq.2 ∈ D via hPS ▸ hPS'? Use simpa.
              simpa only [hPS] using hPS'
            exact Or.inr ⟨h1P, h2D⟩
          · have h1D : pq.1 ∈ Dpool := by
              have hPS' : pq.1 ∈ Ppool \ pool.S :=
                Finset.mem_sdiff.mpr ⟨h1P, h1S⟩
              simpa only [hPS] using hPS'
            exact Or.inl ⟨h1D, h2P⟩
        have hcard_le : (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ) ≤
            ((Dpool ×ˢ Ppool).card : ℝ) + ((Ppool ×ˢ Dpool).card : ℝ) := by
          have h := (Finset.card_le_card hsubA).trans (Finset.card_union_le _ _)
          simp only [Finset.card_product] at h ⊢
          exact_mod_cast h
        have hprod1 : ((Dpool ×ˢ Ppool).card : ℝ) =
            (Dpool.card : ℝ) * (Ppool.card : ℝ) := by
          simp [Finset.card_product]
        have hprod2 : ((Ppool ×ˢ Dpool).card : ℝ) =
            (Ppool.card : ℝ) * (Dpool.card : ℝ) := by
          simp [Finset.card_product]
        calc (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ)
            ≤ ((Dpool ×ˢ Ppool).card : ℝ) + ((Ppool ×ˢ Dpool).card : ℝ) := hcard_le
          _ = (Dpool.card : ℝ) * (Ppool.card : ℝ) +
              (Ppool.card : ℝ) * (Dpool.card : ℝ) := by rw [hprod1, hprod2]
          _ = 2 * (Dpool.card : ℝ) * (Ppool.card : ℝ) := by ring
      -- B bound via retention: |(P×P)\(Ws×Wt)| ≤ ηG·|P|²
      have hBcard : (((Ppool ×ˢ Ppool) \
          (W.sources i ×ˢ W.targets i)).card : ℝ) ≤
          ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
        -- hRetain: ((poolSrc×poolTgt)\(Ws×Wt)).card ≤ ηG·|poolSrc|·|poolTgt|
        -- poolSrc = Ppool definitionally (set), poolTgt = Ppool via hPeq
        have hR := hRetain
        -- Rewrite poolPts targets (in hR) to Ppool via hPeq; poolPts sources is
        -- definitionally Ppool (set/let), so no rewrite needed for it.
        -- hPeq: poolPts targets = Ppool
        have hR' : (((Ppool ×ˢ Ppool) \
            (W.sources i ×ˢ W.targets i)).card : ℝ) ≤
            ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
          have hEq : Ppool ×ˢ TrackD.poolPts (T.targets i) =
              Ppool ×ˢ Ppool := by
            rw [hPeq]
          simpa only [hEq, hPeq] using hR
        exact hR'
      -- C0 bound via list loss: |(Ws×Wt).filter non-list| ≤ ηG·|Ws|·|Wt| ≤ ηG·|P|²
      have hC0card : ((((W.sources i ×ˢ W.targets i).filter (fun pq =>
          W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ)) ≤
          ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
        have hL := hList
        have hWs0 : ((W.sources i).card : ℝ) ≤ (Ppool.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hWsP
        have hWt0 : ((W.targets i).card : ℝ) ≤ (Ppool.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hWtP
        have hnn1 : 0 ≤ ((W.sources i).card : ℝ) := Nat.cast_nonneg _
        have hnn2 : 0 ≤ ((W.targets i).card : ℝ) := Nat.cast_nonneg _
        have hη0 : 0 ≤ ηG := le_of_lt hηGpos
        calc ((((W.sources i ×ˢ W.targets i).filter _).card : ℝ))
            ≤ ηG * ((W.sources i).card : ℝ) * (W.targets i).card := hL
          _ ≤ ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
            have h1 : ηG * ((W.sources i).card : ℝ) ≤ ηG * (Ppool.card : ℝ) :=
              mul_le_mul_of_nonneg_left hWs0 hη0
            calc ηG * ((W.sources i).card : ℝ) * (W.targets i).card
                = (ηG * ((W.sources i).card : ℝ)) * (W.targets i).card := by ring
              _ ≤ (ηG * (Ppool.card : ℝ)) * (W.targets i).card :=
                mul_le_mul_of_nonneg_right h1 hnn2
              _ ≤ (ηG * (Ppool.card : ℝ)) * (Ppool.card : ℝ) :=
                mul_le_mul_of_nonneg_left hWt0 (mul_nonneg hη0 hPcard0)
      -- Filt\G ⊆ A ∪ B ∪ C0
      have hFGsub : Filt \ G ⊆
          ((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)) ∪
          (((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i)) ∪
            ((W.sources i ×ˢ W.targets i).filter (fun pq =>
              W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)))) := by
        intro pq hpq
        have hpq_mem : pq ∈ Filt ∧ pq ∉ G := Finset.mem_sdiff.mp hpq
        obtain ⟨hFilt, hnotG⟩ := hpq_mem
        have hFiltPP' : pq ∈ Ppool ×ˢ Ppool := hFiltPP hFilt
        have hFmem : pq ∈ Filt := hFilt
        have hnotG' : pq ∉ G := hnotG
        simp only [hGdef, Finset.mem_filter] at hnotG'
        -- hnotG': ¬(pq∈Filt ∧ cond); with pq∈Filt, gives ¬cond
        have hcond : ¬ (pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S ∧ pq.1 ∈ W.sources i ∧
            pq.2 ∈ W.targets i ∧ W.owner i pq.2 ∈ L.lists i (W.owner i pq.1)) := by
          intro h
          exact hnotG' ⟨hFilt, h⟩
        by_cases hSS : pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S
        · by_cases hWW : pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i
          · -- must be non-list
            have hnl : W.owner i pq.2 ∉ L.lists i (W.owner i pq.1) := by
              intro hlist
              exact hcond ⟨hSS.1, hSS.2, hWW.1, hWW.2, hlist⟩
            have hWWmem : pq ∈ W.sources i ×ˢ W.targets i :=
              Finset.mem_product.mpr hWW
            have hC0mem : pq ∈ (W.sources i ×ˢ W.targets i).filter (fun pq =>
                W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)) :=
              Finset.mem_filter.mpr ⟨hWWmem, hnl⟩
            exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_union.mpr (Or.inr hC0mem)))
          · -- not in Ws×Wt
            have hBmem : pq ∈ (Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i) :=
              Finset.mem_sdiff.mpr ⟨hFiltPP', by
                intro hWWmem
                exact hWW (Finset.mem_product.mp hWWmem)⟩
            exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_union.mpr (Or.inl hBmem)))
        · -- not in S×S
          have hAmem : pq ∈ (Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S) :=
            Finset.mem_sdiff.mpr ⟨hFiltPP', by
              intro hSSmem
              exact hSS (Finset.mem_product.mp hSSmem)⟩
          exact Finset.mem_union.mpr (Or.inl hAmem)
      -- combine cards: |Filt\G| ≤ |A|+|B|+|C0| ≤ 4ηG·|P|² ≤ ρ'·|S|²
      have hcardFG : ((Filt \ G).card : ℝ) ≤
          (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ) +
          ((((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i)).card : ℝ) +
            ((((W.sources i ×ˢ W.targets i).filter (fun pq =>
              W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ))) := by
        have h := (Finset.card_le_card hFGsub).trans (Finset.card_union_le _ _)
        have h2 := Finset.card_union_le
          ((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i))
          ((W.sources i ×ˢ W.targets i).filter (fun pq =>
            W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)))
        have hle : ((Filt \ G).card : ℝ) ≤
            (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ) +
            (((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i) ∪
              ((W.sources i ×ˢ W.targets i).filter (fun pq =>
                W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)))).card : ℝ) := by
          exact_mod_cast h
        have hle2 : ((((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i) ∪
            ((W.sources i ×ˢ W.targets i).filter (fun pq =>
              W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)))).card : ℝ)) ≤
            (((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i)).card : ℝ) +
              ((((W.sources i ×ˢ W.targets i).filter (fun pq =>
                W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ)) := by
          exact_mod_cast h2
        linarith
      -- bound each by ηG·|P|² (A needs 2ηG)
      have hA2 : (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ) ≤
          2 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
        calc (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ)
            ≤ 2 * (Dpool.card : ℝ) * (Ppool.card : ℝ) := hAcard
          _ ≤ 2 * (ηG * (Ppool.card : ℝ)) * (Ppool.card : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hDsmall (by norm_num))
              (Nat.cast_nonneg _)
          _ = 2 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by ring
      -- total ≤ 4ηG·|P|² ≤ ρ'·|S|² via ηG = ρ'(1-ρ)²/9 and |S| ≥ (1-ρ)|P|
      have htot : ((Filt \ G).card : ℝ) ≤
          4 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
        calc ((Filt \ G).card : ℝ)
            ≤ (((Ppool ×ˢ Ppool) \ (pool.S ×ˢ pool.S)).card : ℝ) +
              ((((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i)).card : ℝ) +
                ((((W.sources i ×ˢ W.targets i).filter (fun pq =>
                  W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ))) :=
              hcardFG
          _ ≤ (2 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ)) +
              (ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) +
                ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ)) :=
              add_le_add hA2 (add_le_add hBcard hC0card)
          _ = 4 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by ring
      have hfinal : ((Filt \ G).card : ℝ) ≤ ρ' * (pool.S.card : ℝ) ^ 2 := by
        have hηGdef : ηG = ρ' * (1 - ρ) ^ 2 / 9 := hηGdef
        have h1mρ0 : 0 ≤ 1 - ρ := le_of_lt h1mρ
        have hSge2 : (1 - ρ) * (Ppool.card : ℝ) ≤ (pool.S.card : ℝ) := hSge
        have hSq : ((1 - ρ) * (Ppool.card : ℝ)) ^ 2 ≤ (pool.S.card : ℝ) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg h1mρ0 hPcard0) hSge2 2
        -- 4ηG·|P|² = 4ρ'(1-ρ)²/9·|P|² ≤ ρ'(1-ρ)²|P|² = ρ'·((1-ρ)|P|)² ≤ ρ'·|S|²
        calc ((Filt \ G).card : ℝ)
            ≤ 4 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := htot
          _ = 4 * (ρ' * (1 - ρ) ^ 2 / 9) * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
              rw [hηGdef]
          _ ≤ ρ' * (1 - ρ) ^ 2 * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
              have h49 : (4 : ℝ) / 9 ≤ 1 := by norm_num
              have hnn : 0 ≤ ρ' * (1 - ρ) ^ 2 * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
                have h1 : 0 ≤ ρ' * (1 - ρ) ^ 2 := by
                  apply mul_nonneg (le_of_lt hρ')
                  exact sq_nonneg _
                exact mul_nonneg (mul_nonneg h1 hPcard0) hPcard0
              calc 4 * (ρ' * (1 - ρ) ^ 2 / 9) * _ * _ =
                  (4 / 9) * (ρ' * (1 - ρ) ^ 2 * _ * _) := by ring
                _ ≤ 1 * (ρ' * (1 - ρ) ^ 2 * _ * _) :=
                  mul_le_mul_of_nonneg_right h49 hnn
                _ = ρ' * (1 - ρ) ^ 2 * _ * _ := by ring
          _ = ρ' * ((1 - ρ) * (Ppool.card : ℝ)) ^ 2 := by ring
          _ ≤ ρ' * (pool.S.card : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hSq (le_of_lt hρ')
      -- Filt\G vs (Sel.filter chart)\G? Filt = Sel.filter chart, G ⊆ Filt, so Filt\G is exactly hGdel's left? hGdel left is ((Sel.filter chart)\G).card = (Filt\G).card. Good (Filt defined as that). Need to rewrite Filt\G to hGdel form (which mentions outerSelectedGraph filter, not Sel/Filt names? But Sel = outerSelectedGraph definitionally via set? Sel set as outerSelectedGraph, Filt set as Sel.filter chart, so Filt\G definitionally = (outerSelectedGraph.filter chart)\G. Good. hGdel expects ((outerSelectedGraph.filter chart)\G).card ≤ ... . Since Filt = that filter (via set, definitionally equal? Filt let-bound? Filt set as Sel.filter..., Sel set as outerSelectedGraph, so Filt definitionally = ...? Via set (let transparent? set uses let? Actually set introduces let, transparent, so definitionally equal. Good. Need to convert (Filt\G).card to ((outerSelectedGraph.filter...)\G).card via rfl? Since Filt/Sel are set (let), they unfold definitionally, so rfl should work? Our hGdel goal is ((Filt\G).card ≤ ...), but OuterChartCert.hGdel expects ((outerSelectedGraph.filter...)\G).card ≤ ... . Since Filt is defined as that filter (via set, transparent? set uses let, so definitionally equal? Actually set introduces local definition with value, so Filt = Sel.filter... definitionally (via let unfolding? For set, the local definition is let-bound, transparent, so unfolding holds definitionally? Good. Similarly Sel = outerSelectedGraph definitionally. So Filt\G definitionally = ... . Good. Our have hGdel proves (Filt\G).card ≤ ..., which definitionally equals required form? Need to ensure final exact uses correct form (with outerSelectedGraph, not Filt). Since they are definitionally equal via let unfolding? For set, the introduced variable is let-bound, so definitional unfolding holds (via delta?). Good. To be safe, use `simpa only [hFiltdef, hSeldef] using hfinal`? Actually hfinal proves (Filt\G).card ≤ ..., need to convert to ((outerSelectedGraph.filter...)\G).card ≤ ... . Since Filt = Sel.filter..., Sel = outerSelectedGraph, unfolding via hFiltdef/hSeldef (which state equalities? set gives hFiltdef : Filt = Sel.filter..., hSeldef : Sel = outerSelectedGraph). Good. So `simpa only [hFiltdef, hSeldef] using hfinal` converts. Good. Let's do that for final hGdel (which currently states (Filt\G).card ≤ ...). Actually our have hGdel already states (Filt\G).card ≤ ..., but OuterChartCert.hGdel expects ((outerSelectedGraph.filter...)\G).card ≤ ... . Since we will use hGdel field in final exact ⟨⟨...⟩⟩, Lean will check definitional equality? It expects specific form with outerSelectedGraph, but we provide proof of (Filt\G).card ≤ ... . Since Filt definitionally = ..., Lean should accept definitionally (since set uses let, transparent). Good. To be safe, state hGdel with outerSelectedGraph form directly (not Filt) to match field exactly (avoid definitional issue). Our current have hGdel states (Filt\G).card ≤ ..., but field expects ((outerSelectedGraph.filter...)\G).card ≤ ... . Since Filt is set as that filter, they are definitionally equal (via let unfolding + set? Actually set introduces Filt as local definition equal to Sel.filter..., Sel as outerSelectedGraph, so Filt unfolds to outerSelectedGraph.filter... definitionally? Via delta (unfold let) + ...? Should hold definitionally, so Lean accepts hGdel where Filt\G used for field expecting outerSelectedGraph.filter...? Since they are definitionally equal, typechecking the final structure with hGdel : (Filt\G).card ≤ ... where field expects ((outerSelectedGraph.filter...)\G).card ≤ ... should succeed if definitionally equal (since Lean checks definitional equality for field types? The field type mentions outerSelectedGraph, our proof has Filt, which unfolds definitionally to same, so Lean should accept as same type? Actually `have hGdel : ((Filt\G).card ≤ ...)` has type mentioning Filt, while field expects type mentioning outerSelectedGraph.filter... . Since Filt is let-bound to that filter, they are definitionally equal, so `exact` should succeed (defeq). Good. To be safe, we proved hfinal for (Filt\G).card, which matches have hGdel's statement (same Filt). Good. No conversion needed for have itself. For final structure, hGdel field expects outerSelectedGraph form, but our hGdel has Filt form – defeq should allow. Good. If fails, use simpa.

      -- For now, admit final conversion via simpa (Filt = Sel.filter..., Sel = outerSelectedGraph)
      simpa only [hFiltdef, hSeldef] using hfinal
    have hmassW : ∀ J : Finset (AffineVariety (d + d)), J ⊆ U →
        ((G.filter (fun pq =>
          commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ J)).card : ℝ) ≤
          Real.exp (ε * M.s i) * (((W.sources i).card : ℝ) * (W.targets i).card /
            (commonCarrierScale M (j + 1) i) ^ 2) *
            ((∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
              (Z.degree : ℚ)) : ℝ) := by
      intro J _
      have hGsubProd : G ⊆ W.sources i ×ˢ W.targets i := by
        intro pq hpq
        simp only [Finset.mem_product]
        exact ⟨(hGpoolsList pq hpq).1, (hGpoolsList pq hpq).2.1⟩
      have hGlist : ∀ pq ∈ G, W.owner i pq.2 ∈ L.lists i (W.owner i pq.1) :=
        fun pq hpq => (hGpoolsList pq hpq).2.2
      have hGchart : ∀ pq ∈ G, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 :=
        hchart
      have hmass := hGraphMass G hGsubProd hGlist hGchart J
      simpa only [hUdef] using hmass
    exact ⟨⟨pool, W, L, hWownF, G, U, hGsub, hGmem, hchart, hGdel, hU,
      hUdeg, hUmem, hlabel, hown, hGpoolsList, hmassW⟩, rfl⟩
  · -- k = 1 (¬ 2 ≤ k): no deletion; S = pool; no flatcap/ratio needed.
    -- Pool via 187b with empty deletion; G/U identical to k ≥ 2; hGdel via
    -- retention/list only (no lowspan/flatcap, no A-part since S = P).
    have hk1 : k = 1 := by omega
    have h1mρ : 0 < 1 - ρ := by linarith
    set ηG : ℝ := ρ' * (1 - ρ) ^ 2 / 9 with hηGdef
    have hηGpos : 0 < ηG := by positivity
    have hRetainEv := common_retained_pair_omissions W ηG hηGpos
    have hListEv := common_list_pair_loss W L ηG hηGpos
    have hBudgetsEv : ∀ᶠ i in atTop, CommonCarrierBudgets W i (ε / 4) :=
      selected_common_carrier_budgets W (by omega) (ε / 4) (by positivity)
    have hCabsorbEv : ∀ᶠ i in atTop, Cdeg ≤ Real.exp ((ε / 2) * M.s i) := by
      have hexp : Filter.Tendsto (fun i => Real.exp ((ε / 2) * M.s i)) atTop atTop :=
        Real.tendsto_exp_atTop.comp
          (M.width_grows.const_mul_atTop (half_pos hε))
      exact hexp.eventually (Filter.eventually_ge_atTop Cdeg)
    filter_upwards [hRetainEv, hListEv, hLmassEv, hBudgetsEv, hCabsorbEv] with i
      hRetain hList hLmass hBudgets hCabsorb
    have hLmass0 := hLmass i₀
    -- trivial pool S = P (no deletion at k = 1)
    set Ppool : Finset (RPoint d) := TrackD.poolPts (T.sources i) with hPpooldef
    set Spool : Finset (RPoint d) := Ppool with hSpooldef
    set Rpool : Finset (AffineVariety d × AffineVariety d) :=
      (outerSelectedGraph T i).image
        (fun pq => (W.owner i pq.1, W.owner i pq.2)) with hRpooldef
    have hownsup : TrackD.CarrierAssignment (T.sources i ∪ T.targets i) (j + 1)
        (W.owner i) := W.supported i
    have hj1le : j + 1 ≤ d := by omega
    have hdim_eq : d - (j + 1) = k := by omega
    have hpiece_good : ∀ X ∈ T.sources i ∪ T.targets i,
        TrackD.PieceGood (regime.P i) (selectionTolerance (T.precision i))
          (selectionTolerance (T.precision i)) (selectionScale (T.precision i)) X := by
      intro X hX
      have hmem : X ∈ (T.partition i).pieces := by
        rcases Finset.mem_union.mp hX with h | h
        · exact (T.certificate i).sources_subset h
        · exact (T.certificate i).targets_subset h
      exact ((T.certificate i).good.pieces_good X hmem).1
    have hown_pure : ∀ q : RPoint d, ∀ X : TrackD.Piece d,
        X ∈ T.sources i ∪ T.targets i → q ∈ X.pts →
        (W.owner i q).IsIrreducible ∧ (W.owner i q).dimension = k := by
      intro q X hXmem hqmem
      obtain ⟨hcarr, hpt⟩ := hownsup X hXmem q hqmem
      have hgood := hpiece_good X hXmem
      have hvan : ∀ a : Fin d,
          MvPolynomial.eval (TrackD.toC q) (X.path.cut a) = 0 :=
        fun a => hgood.vanish q hqmem a
      have hprop : X.path.ProperAt (TrackD.toC q) := hgood.proper q hqmem
      have hlocal : W.owner i q ∈ X.path.localCarriers (j + 1) (TrackD.toC q) :=
        ⟨hcarr, hpt⟩
      have hpure := TrackD.prof_partition_pure X q hqmem hvan hprop
        (j + 1) hj1le (W.owner i q) hlocal
      rw [hdim_eq] at hpure
      exact hpure
    have hRpure : ∀ r ∈ Rpool,
        r.1.IsIrreducible ∧ r.1.dimension = k ∧
        r.2.IsIrreducible ∧ r.2.dimension = k := by
      intro r hr
      simp only [hRpooldef, Finset.mem_image] at hr
      obtain ⟨pq, hpq, rfl⟩ := hr
      have h1P : pq.1 ∈ Ppool := by
        simp only [outerSelectedGraph, Finset.mem_filter, Finset.mem_product,
          hPpooldef] at hpq
        exact hpq.1.1
      have h2P : pq.2 ∈ TrackD.poolPts (T.targets i) := by
        simp only [outerSelectedGraph, Finset.mem_filter, Finset.mem_product] at hpq
        exact hpq.1.2
      obtain ⟨X1, hX1mem, hq1mem⟩ := Finset.mem_biUnion.mp h1P
      have hX1union : X1 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hX1mem
      have hpure1 := hown_pure pq.1 X1 hX1union hq1mem
      obtain ⟨X2, hX2mem, hq2mem⟩ := Finset.mem_biUnion.mp h2P
      have hX2union : X2 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_right _ hX2mem
      have hpure2 := hown_pure pq.2 X2 hX2union hq2mem
      exact ⟨hpure1.1, hpure1.2, hpure2.1, hpure2.2⟩
    have hRirr : ∀ r ∈ Rpool, r.1.IsIrreducible ∧ r.2.IsIrreducible := by
      intro r hr
      obtain ⟨h1, _, h2, _⟩ := hRpure r hr
      exact ⟨h1, h2⟩
    have hRdim : ∀ r ∈ Rpool, r.1.dimension = k ∧ r.2.dimension = k := by
      intro r hr
      obtain ⟨_, h1, _, h2⟩ := hRpure r hr
      exact ⟨h1, h2⟩
    have hownfull : ∀ pq ∈ outerSelectedGraph T i,
        ∃ r ∈ Rpool, W.owner i pq.1 = r.1 ∧ W.owner i pq.2 = r.2 := by
      intro pq hpq
      exact ⟨(W.owner i pq.1, W.owner i pq.2),
        Finset.mem_image.mpr ⟨pq, hpq, rfl⟩, rfl, rfl⟩
    -- hspan vacuous at k = 1 (must NOT use the flat cap)
    have hspan : 2 ≤ k → ∀ q ∈ Spool,
        ¬ ∃ Ff : AffineSubspace ℂ (Point d),
          Module.finrank ℂ Ff.direction ≤ k + 1 ∧ (W.owner i q).points ⊆ ↑Ff := by
      intro h2
      exact absurd h2 hk2
    -- hScard trivial: (1-ρ)|P| ≤ |P| = |S|
    have hScard : (1 - ρ) * (Ppool.card : ℝ) ≤ (Spool.card : ℝ) := by
      have hP0 : 0 ≤ (Ppool.card : ℝ) := Nat.cast_nonneg _
      have hle : (1 - ρ : ℝ) ≤ 1 := by linarith [hρ]
      calc (1 - ρ) * (Ppool.card : ℝ) ≤ 1 * (Ppool.card : ℝ) :=
            mul_le_mul_of_nonneg_right hle hP0
        _ = (Spool.card : ℝ) := by
            simp only [hSpooldef, one_mul]
    have hSsub_goal : Spool ⊆ TrackD.poolPts (T.sources i) := by
      simpa only [hSpooldef, hPpooldef] using Finset.Subset.rfl
    have hScard_goal : (1 - ρ) * ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
        (Spool.card : ℝ) := by
      simpa only [hPpooldef] using hScard
    let pool : OuterPoolData T M k i j ρ ε :=
      ⟨Spool, Rpool, W.owner i, hkj, hSsub_goal, hScard_goal, hownsup,
        hRirr, hRdim, hownfull, hspan⟩
    -- outer pools coincide
    have hSTEq : T.targets i = T.sources i := (houter i).1.symm
    set Sel : Finset (RPoint d × RPoint d) := outerSelectedGraph T i with hSeldef
    set Filt : Finset (RPoint d × RPoint d) := Sel.filter (fun pq =>
      (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) with hFiltdef
    set G : Finset (RPoint d × RPoint d) := Filt.filter (fun pq =>
      pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S ∧ pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
        W.owner i pq.2 ∈ L.lists i (W.owner i pq.1)) with hGdef
    set U : Finset (AffineVariety (d + d)) :=
      commonChartImages W L i i₀ with hUdef
    obtain ⟨hUpure, hGraphMass⟩ := hLmass0
    have hUpure2k : AffineFamily.IsPure U (2 * k) := by
      have hdk2 : d - (j + 1) = k := by omega
      simpa only [hUdef, hdk2] using hUpure
    have hGsub : G ⊆ outerSelectedGraph T i := by
      simp only [hGdef, hFiltdef, hSeldef]
      exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hGmem : ∀ pq ∈ G, pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S := by
      intro pq hpq
      simp only [hGdef, Finset.mem_filter] at hpq
      exact ⟨hpq.2.1, hpq.2.2.1⟩
    have hchart : ∀ pq ∈ G, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
      intro pq hpq
      simp only [hGdef, hFiltdef, Finset.mem_filter] at hpq
      exact hpq.1.2
    have hGpoolsList : ∀ pq ∈ G, pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
        W.owner i pq.2 ∈ L.lists i (W.owner i pq.1) := by
      intro pq hpq
      simp only [hGdef, Finset.mem_filter] at hpq
      exact ⟨hpq.2.2.2.1, hpq.2.2.2.2.1, hpq.2.2.2.2.2⟩
    have hWownF : ∀ q : TrackD.Pt d, W.owner i q = pool.own q := fun q => rfl
    have hown : ∀ pq ∈ G, ∃ r ∈ pool.R, pool.own pq.1 = r.1 ∧ pool.own pq.2 = r.2 := by
      intro pq hpq
      have hpqSel : pq ∈ outerSelectedGraph T i := hGsub hpq
      obtain ⟨r, hr, h1, h2⟩ := pool.hownfull pq hpqSel
      exact ⟨r, hr, h1, h2⟩
    have hU : ∀ W0 ∈ U, W0.IsIrreducible ∧ W0.dimension = 2 * k := by
      intro W0 hW0
      exact hUpure2k W0 hW0
    have hUdeg : ((AffineFamily.degree U : ℚ) : ℝ) ≤
        (1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
          Real.exp (ε * M.s i) := by
      have hpair : ∀ X ∈ W.sourceCarriers i, ∀ Y ∈ L.lists i X,
          X.IsIrreducible → X.dimension = k → Y.IsIrreducible → Y.dimension = k →
          (∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) →
          ((commonProductImage i₀ X Y).degree : ℝ) ≤
            Cdeg * (X.degree : ℝ) * (Y.degree : ℝ) := by
        intro X hX Y hY hXi hXd hYi hYd hch
        have hZmem : commonProductImage i₀ X Y ∈ U := by
          simp only [hUdef, commonChartImages, Finset.mem_biUnion]
          refine ⟨X, hX, Finset.mem_image.mpr ⟨Y, ?_, rfl⟩⟩
          exact Finset.mem_filter.mpr ⟨hY, hch⟩
        exact hCpair X Y hXi hXd hYi hYd hch (hUpure2k _ hZmem).2
      have hfam := mo_chart_family_degree_le W L k hk.1 (by omega : d - (j + 1) = k)
        (by omega : j + 1 ≤ d) i i₀ ρ hρ hε Cdeg hCdeg hpair hBudgets hUpure2k hCabsorb
      simpa only [commonCarrierScale] using hfam
    have hUmem : ∀ pq ∈ G, commonProductImage i₀ (W.owner i pq.1)
        (W.owner i pq.2) ∈ U := by
      intro pq hpq
      have hWsWt := hGpoolsList pq hpq
      obtain ⟨hWs, hWt, hlist⟩ := hWsWt
      have hch := hchart pq hpq
      have hXmem : W.owner i pq.1 ∈ W.sourceCarriers i := by
        simp only [CommonPhysicalSequence.sourceCarriers, commonOwnerFamily]
        exact Finset.mem_image.mpr ⟨pq.1, hWs, rfl⟩
      have hPsrc1 : pq.1 ∈ TrackD.poolPts (T.sources i) := by
        have hsub : W.sources i ⊆ TrackD.poolPts (T.sources i) :=
          Finset.filter_subset _ _
        exact hsub hWs
      have hPsrc2 : pq.2 ∈ TrackD.poolPts (T.targets i) := by
        have hsub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
          Finset.filter_subset _ _
        exact hsub hWt
      obtain ⟨X1, hX1mem, hq1mem⟩ := Finset.mem_biUnion.mp hPsrc1
      have hX1union : X1 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hX1mem
      obtain ⟨_, hpt1⟩ := W.supported i X1 hX1union pq.1 hq1mem
      obtain ⟨X2, hX2mem, hq2mem⟩ := Finset.mem_biUnion.mp hPsrc2
      have hX2union : X2 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_right _ hX2mem
      obtain ⟨_, hpt2⟩ := W.supported i X2 hX2union pq.2 hq2mem
      have hYchart : W.owner i pq.2 ∈
          commonChartTargets W L i i₀ (W.owner i pq.1) := by
        simp only [commonChartTargets, Finset.mem_filter]
        refine ⟨hlist, ?_⟩
        exact ⟨TrackD.toC pq.1, hpt1, TrackD.toC pq.2, hpt2, hch⟩
      simp only [hUdef, commonChartImages, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨W.owner i pq.1, hXmem, W.owner i pq.2, hYchart, rfl⟩
    have hlabel : ∀ pq ∈ G, (fun kk =>
        TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
          (finSumFinEquiv.symm kk)) ∈
            (commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)).points := by
      intro pq hpq
      have hch := hchart pq hpq
      have hWsWt := hGpoolsList pq hpq
      obtain ⟨hWs, hWt, -⟩ := hWsWt
      have hPsrc1 : pq.1 ∈ TrackD.poolPts (T.sources i) := by
        have hsub : W.sources i ⊆ TrackD.poolPts (T.sources i) :=
          Finset.filter_subset _ _
        exact hsub hWs
      have hPsrc2 : pq.2 ∈ TrackD.poolPts (T.targets i) := by
        have hsub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
          Finset.filter_subset _ _
        exact hsub hWt
      obtain ⟨X1, hX1mem, hq1mem⟩ := Finset.mem_biUnion.mp hPsrc1
      have hX1union : X1 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_left _ hX1mem
      obtain ⟨_, hpt1⟩ := W.supported i X1 hX1union pq.1 hq1mem
      obtain ⟨X2, hX2mem, hq2mem⟩ := Finset.mem_biUnion.mp hPsrc2
      have hX2union : X2 ∈ T.sources i ∪ T.targets i :=
        Finset.mem_union_right _ hX2mem
      obtain ⟨_, hpt2⟩ := W.supported i X2 hX2union pq.2 hq2mem
      have hleft_eq : TrackD.productLeft
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) =
          TrackD.toC pq.1 := by
        funext i
        simp only [TrackD.productLeft, TrackD.productPoint_inl]
      have hright_eq : TrackD.productRight
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) =
          TrackD.toC pq.2 := by
        funext i
        simp only [TrackD.productRight, TrackD.productPoint_inr]
      have hprodmem : TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2) ∈
          (TrackD.productVariety (W.owner i pq.1) (W.owner i pq.2)).points := by
        rw [TrackD.productVariety_points]
        simp only [Set.mem_setOf_eq]
        rw [hleft_eq, hright_eq]
        exact ⟨hpt1, hpt2⟩
      have hdenom : MvPolynomial.eval
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2))
          (TrackD.secantChartDenominator i₀) ≠ 0 := by
        rw [TrackD.eval_secantChartDenominator]
        exact hch
      have hmem : TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀)
          (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) ∈
          (commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)).points := by
        simp only [commonProductImage]
        exact TrackD.rationalPoint_mem_image _ _ _
          _ hprodmem hdenom
      have hsec := TrackD.rational_secant_label i₀
        (TrackD.toC pq.1) (TrackD.toC pq.2) hch
      have hlabel_eq : (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1)
          (TrackD.toC pq.2) (finSumFinEquiv.symm kk)) =
          TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀)
            (TrackD.productPoint (TrackD.toC pq.1) (TrackD.toC pq.2)) := by
        simp only [TrackD.labelPt, hsec]
        rfl
      rw [hlabel_eq]
      exact hmem
    -- hGdel at k = 1: S = P, so no A-part; B (retention) + C0 (list) only.
    have hGdel : (((outerSelectedGraph T i).filter (fun pq =>
        (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)) \ G).card ≤
        ρ' * (pool.S.card : ℝ) ^ 2 := by
      have hPeq : TrackD.poolPts (T.targets i) = Ppool := by
        rw [hSTEq]
      have hSeq : pool.S = Ppool := rfl
      have hPcard0 : 0 ≤ (Ppool.card : ℝ) := Nat.cast_nonneg _
      have hWsP : W.sources i ⊆ Ppool := Finset.filter_subset _ _
      have hWtP : W.targets i ⊆ Ppool := by
        have hsub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
          Finset.filter_subset _ _
        simpa only [hPeq] using hsub
      have hSelPP : Sel ⊆ Ppool ×ˢ Ppool := by
        intro pq hpq
        simp only [hSeldef, outerSelectedGraph, Finset.mem_filter,
          Finset.mem_product] at hpq ⊢
        obtain ⟨⟨h1, h2⟩, -⟩ := hpq
        refine ⟨h1, ?_⟩
        rw [← hPeq]
        exact h2
      have hFiltPP : Filt ⊆ Ppool ×ˢ Ppool :=
        (Finset.filter_subset _ _).trans hSelPP
      have hBcard : (((Ppool ×ˢ Ppool) \
          (W.sources i ×ˢ W.targets i)).card : ℝ) ≤
          ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
        have hR := hRetain
        have hEq : Ppool ×ˢ TrackD.poolPts (T.targets i) =
            Ppool ×ˢ Ppool := by
          rw [hPeq]
        simpa only [hEq, hPeq] using hR
      have hC0card : ((((W.sources i ×ˢ W.targets i).filter (fun pq =>
          W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ)) ≤
          ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
        have hL := hList
        have hWs0 : ((W.sources i).card : ℝ) ≤ (Ppool.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hWsP
        have hWt0 : ((W.targets i).card : ℝ) ≤ (Ppool.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hWtP
        have hnn1 : 0 ≤ ((W.sources i).card : ℝ) := Nat.cast_nonneg _
        have hnn2 : 0 ≤ ((W.targets i).card : ℝ) := Nat.cast_nonneg _
        have hη0 : 0 ≤ ηG := le_of_lt hηGpos
        calc ((((W.sources i ×ˢ W.targets i).filter _).card : ℝ))
            ≤ ηG * ((W.sources i).card : ℝ) * (W.targets i).card := hL
          _ ≤ ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
            have h1 : ηG * ((W.sources i).card : ℝ) ≤ ηG * (Ppool.card : ℝ) :=
              mul_le_mul_of_nonneg_left hWs0 hη0
            calc ηG * ((W.sources i).card : ℝ) * (W.targets i).card
                = (ηG * ((W.sources i).card : ℝ)) * (W.targets i).card := by ring
              _ ≤ (ηG * (Ppool.card : ℝ)) * (W.targets i).card :=
                mul_le_mul_of_nonneg_right h1 hnn2
              _ ≤ (ηG * (Ppool.card : ℝ)) * (Ppool.card : ℝ) :=
                mul_le_mul_of_nonneg_left hWt0 (mul_nonneg hη0 hPcard0)
      -- Filt\G ⊆ B ∪ C0 (S = P, so the S×S condition is automatic)
      have hFGsub : Filt \ G ⊆
          (((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i)) ∪
            ((W.sources i ×ˢ W.targets i).filter (fun pq =>
              W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)))) := by
        intro pq hpq
        have hpq_mem : pq ∈ Filt ∧ pq ∉ G := Finset.mem_sdiff.mp hpq
        obtain ⟨hFilt, hnotG⟩ := hpq_mem
        have hFiltPP' : pq ∈ Ppool ×ˢ Ppool := hFiltPP hFilt
        simp only [hGdef, Finset.mem_filter] at hnotG
        have hSS : pq.1 ∈ pool.S ∧ pq.2 ∈ pool.S := by
          have hmem := Finset.mem_product.mp hFiltPP'
          rw [hSeq]
          exact hmem
        have hcond : ¬ (pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
            W.owner i pq.2 ∈ L.lists i (W.owner i pq.1)) := by
          intro h
          exact hnotG ⟨hFilt, hSS.1, hSS.2, h.1, h.2.1, h.2.2⟩
        by_cases hWW : pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i
        · have hnl : W.owner i pq.2 ∉ L.lists i (W.owner i pq.1) := by
            intro hlist
            exact hcond ⟨hWW.1, hWW.2, hlist⟩
          have hWWmem : pq ∈ W.sources i ×ˢ W.targets i :=
            Finset.mem_product.mpr hWW
          have hC0mem : pq ∈ (W.sources i ×ˢ W.targets i).filter (fun pq =>
              W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)) :=
            Finset.mem_filter.mpr ⟨hWWmem, hnl⟩
          exact Finset.mem_union.mpr (Or.inr hC0mem)
        · have hBmem : pq ∈ (Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i) :=
            Finset.mem_sdiff.mpr ⟨hFiltPP', by
              intro hWWmem
              exact hWW (Finset.mem_product.mp hWWmem)⟩
          exact Finset.mem_union.mpr (Or.inl hBmem)
      have hcardFG : ((Filt \ G).card : ℝ) ≤
          ((((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i)).card : ℝ) +
            ((((W.sources i ×ˢ W.targets i).filter (fun pq =>
              W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ))) := by
        have h := (Finset.card_le_card hFGsub).trans (Finset.card_union_le _ _)
        exact_mod_cast h
      have htot : ((Filt \ G).card : ℝ) ≤
          2 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by
        calc ((Filt \ G).card : ℝ)
            ≤ ((((Ppool ×ˢ Ppool) \ (W.sources i ×ˢ W.targets i)).card : ℝ) +
              ((((W.sources i ×ˢ W.targets i).filter (fun pq =>
                W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ))) := hcardFG
          _ ≤ (ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) +
              ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ)) :=
              add_le_add hBcard hC0card
          _ = 2 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := by ring
      have h2η : 2 * ηG ≤ ρ' := by
        have hsq : (1 - ρ) ^ 2 ≤ 1 := by
          have h1 : 0 ≤ 1 - ρ := le_of_lt h1mρ
          have h2 : 1 - ρ ≤ 1 := by linarith [hρ]
          calc (1 - ρ) ^ 2 = (1 - ρ) * (1 - ρ) := by ring
            _ ≤ 1 * 1 := mul_le_mul h2 h2 h1 (by norm_num)
            _ = 1 := mul_one 1
        calc 2 * ηG = ρ' * (2 * (1 - ρ) ^ 2 / 9) := by rw [hηGdef]; ring
          _ ≤ ρ' * 1 := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hρ')
            calc (2 : ℝ) * (1 - ρ) ^ 2 / 9 ≤ 2 * 1 / 9 := by linarith [hsq]
              _ = 2 / 9 := by ring
              _ ≤ 1 := by norm_num
          _ = ρ' := mul_one _
      have hfinal : ((Filt \ G).card : ℝ) ≤ ρ' * (pool.S.card : ℝ) ^ 2 := by
        have hSq : (pool.S.card : ℝ) = (Ppool.card : ℝ) := by rw [hSeq]
        calc ((Filt \ G).card : ℝ)
            ≤ 2 * ηG * (Ppool.card : ℝ) * (Ppool.card : ℝ) := htot
          _ = (2 * ηG) * ((Ppool.card : ℝ) * (Ppool.card : ℝ)) := by ring
          _ ≤ ρ' * ((Ppool.card : ℝ) * (Ppool.card : ℝ)) :=
              mul_le_mul_of_nonneg_right h2η
                (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          _ = ρ' * (pool.S.card : ℝ) ^ 2 := by rw [hSq]; ring
      simpa only [hFiltdef, hSeldef] using hfinal
    have hmassW : ∀ J : Finset (AffineVariety (d + d)), J ⊆ U →
        ((G.filter (fun pq =>
          commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ J)).card : ℝ) ≤
          Real.exp (ε * M.s i) * (((W.sources i).card : ℝ) * (W.targets i).card /
            (commonCarrierScale M (j + 1) i) ^ 2) *
            ((∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
              (Z.degree : ℚ)) : ℝ) := by
      intro J _
      have hGsubProd : G ⊆ W.sources i ×ˢ W.targets i := by
        intro pq hpq
        simp only [Finset.mem_product]
        exact ⟨(hGpoolsList pq hpq).1, (hGpoolsList pq hpq).2.1⟩
      have hGlist : ∀ pq ∈ G, W.owner i pq.2 ∈ L.lists i (W.owner i pq.1) :=
        fun pq hpq => (hGpoolsList pq hpq).2.2
      have hGchart : ∀ pq ∈ G, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 :=
        hchart
      have hmass := hGraphMass G hGsubProd hGlist hGchart J
      simpa only [hUdef] using hmass
    exact ⟨⟨pool, W, L, hWownF, G, U, hGsub, hGmem, hchart, hGdel, hU,
      hUdeg, hUmem, hlabel, hown, hGpoolsList, hmassW⟩, rfl⟩
end
end DistinctDistances.SparseCones
