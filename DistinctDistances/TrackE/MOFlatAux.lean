import DistinctDistances.TrackE.Basic
import DistinctDistances.TrackE.ComplexSpan
import DistinctDistances.TrackE.SelectionSequence
import DistinctDistances.TrackE.CommonProfiles
import DistinctDistances.TrackE.FlatCaps
import DistinctDistances.TrackE.WindowBranches

/-! Helpers for the outer flat cap. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

-- Pool points lie in the global configuration.
theorem mo_pool_subset_global {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (i : ℕ) :
    TrackD.poolPts (T.sources i) ⊆ regime.P i := by
  intro x hx
  obtain ⟨X, hXmem, hxmem⟩ := Finset.mem_biUnion.mp hx
  have hsub : X ∈ (T.partition i).pieces :=
    (T.certificate i).sources_subset hXmem
  have hgood := ((T.certificate i).good.pieces_good X hsub).1
  exact hgood.subset hxmem

-- Real-independent vectors stay complex-independent after `cplx`.
theorem mo_cplx_preserves_independence {r : ℕ} (v : Fin r → RPoint d)
    (h : LinearIndependent ℝ v) :
    LinearIndependent ℂ (fun i => cplx (v i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  -- Decompose coefficients into real/imaginary parts.
  set a : Fin r → ℝ := fun j => (g j).re with ha
  set b : Fin r → ℝ := fun j => (g j).im with hb
  have hg0 : ∑ j, g j • cplx (v j) = 0 := hg
  -- Take coordinates: for each `k`, `∑ j, g j * (v j k : ℂ) = 0`.
  have hcoord : ∀ k : Fin d, ∑ j, g j * ((v j k : ℝ) : ℂ) = 0 := by
    intro k
    have := congrFun hg0 k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cplx] using this
  -- Real parts vanish coordinate-wise.
  have hre : ∀ k : Fin d, ∑ j, a j * (v j k) = 0 := by
    intro k
    have h0 := hcoord k
    have hre0 : (∑ j, g j * ((v j k : ℝ) : ℂ)).re = 0 := by rw [h0]; rfl
    rw [Complex.re_sum] at hre0
    have hexpand : ∀ j : Fin r, (g j * ((v j k : ℝ) : ℂ)).re = a j * (v j k) := by
      intro j
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      simp [ha]
    have hre1 : ∑ j : Fin r, (g j * ((v j k : ℝ) : ℂ)).re
        = ∑ j, a j * (v j k) :=
      Finset.sum_congr rfl (fun j _ => hexpand j)
    rw [hre1] at hre0
    exact hre0
  have him : ∀ k : Fin d, ∑ j, b j * (v j k) = 0 := by
    intro k
    have h0 := hcoord k
    have him0 : (∑ j, g j * ((v j k : ℝ) : ℂ)).im = 0 := by rw [h0]; rfl
    rw [Complex.im_sum] at him0
    have hexpand : ∀ j : Fin r, (g j * ((v j k : ℝ) : ℂ)).im = b j * (v j k) := by
      intro j
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      simp [hb]
    have him1 : ∑ j : Fin r, (g j * ((v j k : ℝ) : ℂ)).im
        = ∑ j, b j * (v j k) :=
      Finset.sum_congr rfl (fun j _ => hexpand j)
    rw [him1] at him0
    exact him0
  -- Therefore the real linear combinations vanish.
  have ha0 : ∑ j, a j • v j = 0 := by
    ext k
    have hproj : (EuclideanSpace.projₗ k) (∑ j, a j • v j)
        = ∑ j, a j * (v j k) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      rfl
    have hzero : (EuclideanSpace.projₗ k) (∑ j, a j • v j) = 0 := by
      rw [hproj]
      exact hre k
    simpa using hzero
  have hb0 : ∑ j, b j • v j = 0 := by
    ext k
    have hproj : (EuclideanSpace.projₗ k) (∑ j, b j • v j)
        = ∑ j, b j * (v j k) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      rfl
    have hzero : (EuclideanSpace.projₗ k) (∑ j, b j • v j) = 0 := by
      rw [hproj]
      exact him k
    simpa using hzero
  have ha_i := Fintype.linearIndependent_iff.mp h a ha0 i
  have hb_i := Fintype.linearIndependent_iff.mp h b hb0 i
  have hgi : g i = ((a i : ℝ) : ℂ) + ((b i : ℝ) : ℂ) * Complex.I := by
    rw [ha, hb]
    exact (Complex.re_add_im (g i)).symm
  rw [hgi, ha_i, hb_i]
  simp

-- A real subspace whose `cplx`-image lies in a complex subspace is no larger.
theorem mo_span_dim_le (V : Submodule ℝ (RPoint d)) (W : Submodule ℂ (Point d))
    (h : ∀ v ∈ V, cplx v ∈ W) :
    Module.finrank ℝ V ≤ Module.finrank ℂ W := by
  classical
  set r := Module.finrank ℝ V with hr
  set b := Module.finBasis ℝ V with hb
  set v : Fin r → RPoint d := fun i => ((b i : V) : RPoint d) with hv
  have hv_eq : v = fun i => V.subtype (b i) := rfl
  have hv_indep : LinearIndependent ℝ v := by
    rw [hv_eq]
    exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hw_indep : LinearIndependent ℂ (fun i => cplx (v i)) :=
    mo_cplx_preserves_independence v hv_indep
  have hw_mem : ∀ i, cplx (v i) ∈ W := fun i => h _ (b i).property
  have hspan_le : Submodule.span ℂ (Set.range (fun i => cplx (v i))) ≤ W :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hw_mem)
  have hcard : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => cplx (v i))))
      = r := by
    have hfin := finrank_span_eq_card hw_indep
    simpa [Fintype.card_fin] using hfin
  calc Module.finrank ℝ V = r := rfl
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => cplx (v i)))) :=
        hcard.symm
    _ ≤ Module.finrank ℂ W := Submodule.finrank_mono hspan_le

-- The real affine span of points in a complex flat has dimension at most the flat's.
theorem mo_affine_dim_le (S : Finset (RPoint d)) (Ff : AffineSubspace ℂ (Point d))
    (hmem : ∀ q ∈ S, cplx q ∈ Ff) :
    Module.finrank ℝ (affineSpan ℝ (↑S : Set (RPoint d))).direction ≤
      Module.finrank ℂ Ff.direction := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨p0, hp0⟩ := hS
    have hp0mem : p0 ∈ (↑S : Set (RPoint d)) := Finset.mem_coe.mpr hp0
    have hp0F : cplx p0 ∈ Ff := hmem p0 hp0
    have hdir_eq : (affineSpan ℝ (↑S : Set (RPoint d))).direction
        = vectorSpan ℝ (↑S : Set (RPoint d)) := direction_affineSpan ℝ _
    rw [hdir_eq, vectorSpan_eq_span_vsub_set_right ℝ hp0mem]
    apply mo_span_dim_le _ _ ?_
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro x ⟨q, hq, rfl⟩
      have hqmem : q ∈ (↑S : Set (RPoint d)) := hq
      have hqS : q ∈ S := Finset.mem_coe.mp hqmem
      have hqF : cplx q ∈ Ff := hmem q hqS
      have hdiff : cplx (q -ᵥ p0) = cplx q - cplx p0 := by
        ext i
        simp [cplx, vsub_eq_sub]
      have hsub : cplx q - cplx p0 ∈ Ff.direction := by
        have hvs : cplx q -ᵥ cplx p0 ∈ Ff.direction :=
          AffineSubspace.vsub_mem_direction hqF hp0F
        rwa [vsub_eq_sub] at hvs
      rw [hdiff]
      exact hsub
    · have hzero : cplx (0 : RPoint d) = 0 := by ext i; simp [cplx]
      rw [hzero]
      exact Ff.direction.zero_mem
    · intro x y hx hy hxW hyW
      have hadd : cplx (x + y) = cplx x + cplx y := by ext i; simp [cplx]
      rw [hadd]
      exact Ff.direction.add_mem hxW hyW
    · intro a x hx ih
      have hsmul : cplx (a • x) = (a : ℂ) • cplx x := by ext i; simp [cplx]
      rw [hsmul]
      exact Ff.direction.smul_mem _ ih
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    have hempty : ((∅ : Finset (RPoint d)) : Set (RPoint d)) = ∅ := Finset.coe_empty
    rw [hempty, direction_affineSpan ℝ ∅, vectorSpan_empty, finrank_bot]
    exact Nat.zero_le _

-- The outer flat cap for `k ≥ 2` (the case used by the assembly).
-- For `k = 1` the plane case needs the sharp `B^{2+o(1))}` bound, unavailable
-- from the weak `C M^{4/3}` input when `ε < 2/3`.
theorem mo_outer_flat_cap_aux {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (houter : ∀ i, T.IsOuter i) (hs : ∀ i, M.s i = Real.log (regime.B i))
    (k : ℕ) (hk : 1 ≤ k ∧ k + 1 < d)
    (ε : ℝ) (hε : 0 < ε) (hk2 : 2 ≤ k) :
    ∀ᶠ i in atTop, ∀ Ff : AffineSubspace ℂ (Point d),
      Module.finrank ℂ Ff.direction ≤ k + 1 →
      (((TrackD.poolPts (T.sources i)).filter
        (fun q => TrackD.toC q ∈ Ff)).card : ℝ) ≤
        (regime.B i) ^ (k + 1) * Real.exp (ε * M.s i) := by
  classical
  have hd : 3 ≤ d := regime.dimension_ge_three
  have hIH : IH d := regime.inductionHypothesis
  have hk1 : 1 ≤ k := hk.1
  have hkd : k + 1 < d := hk.2
  have hk3 : 3 ≤ k + 1 := by omega
  -- Plane constant.
  obtain ⟨Cplane, hCplane, hplane⟩ := Reduction.card_inter_plane_le (d := d)
  -- Rpow thresholds for each `u` with `3 ≤ u ≤ k+1`.
  -- For each such `u`, get `N₀ u`.
  have hrpow : ∀ u : ℕ, 3 ≤ u → u < d →
      ∃ N₀ : ℕ, ∀ P : Finset (RPoint d), N₀ ≤ P.card →
        Mcount P ≤ Ascale d P.card →
        ∀ F : AffineSubspace ℝ (RPoint d), Module.finrank ℝ F.direction = u →
          ((P.filter (· ∈ F)).card : ℝ) ≤ Bscale d P.card ^ ((u : ℝ) + ε) := by
    intro u hu3 hud
    exact Reduction.card_inter_flat_le_rpow hd hIH u hu3 hud ε hε
  choose N0 hN0 using hrpow
  -- Uniform `N₀` as max over `u ∈ range (k+2)`.
  set Nmax : ℕ := (Finset.range (k + 2)).sup (fun u => if h : 3 ≤ u ∧ u < d then N0 u h.1 h.2 else 0) with hNmax
  have hNmax_ge : ∀ (u : ℕ) (hu3 : 3 ≤ u) (hud : u < d) (hult : u < k + 2),
      N0 u hu3 hud ≤ Nmax := by
    intro u hu3 hud hult
    have hmem : u ∈ Finset.range (k + 2) := Finset.mem_range.mpr hult
    have hle := Finset.le_sup hmem (f := fun u => if h : 3 ≤ u ∧ u < d then N0 u h.1 h.2 else 0)
    have hif : (if h : 3 ≤ u ∧ u < d then N0 u h.1 h.2 else 0) = N0 u hu3 hud := by
      simp [hu3, hud]
    rw [hif] at hle
    exact hle
  -- Eventually: `M ≤ A`, `Nmax ≤ card`, `B ≥ 1`, and `B`-growth for constants.
  have hevM : ∀ᶠ i in atTop, regime.M i ≤ regime.A i := regime.eventually_M_le_A
  have hevCard : ∀ᶠ i in atTop, Nmax ≤ (regime.P i).card :=
    regime.card_tendsto.eventually (eventually_ge_atTop Nmax)
  have hevB1 : ∀ᶠ i in atTop, 1 ≤ regime.B i := by
    filter_upwards [regime.B_tendsto.eventually (eventually_ge_atTop 1)] with i hi
    exact hi
  -- `B ^ δ → ∞` for the two gaps we need.
  have hgap_line : (0 : ℝ) < (k : ℝ) - 1 + ε := by
    have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hgap_plane : (0 : ℝ) < (k : ℝ) + 1 + ε - 8 / 3 := by
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hevLine : ∀ᶠ i in atTop, (2 : ℝ) ≤ (regime.B i) ^ ((k : ℝ) - 1 + ε) := by
    have htend : Tendsto (fun i => (regime.B i) ^ ((k : ℝ) - 1 + ε)) atTop atTop :=
      (tendsto_rpow_atTop hgap_line).comp regime.B_tendsto
    exact htend.eventually (eventually_ge_atTop 2)
  have hevPlane : ∀ᶠ i in atTop, Cplane ≤ (regime.B i) ^ ((k : ℝ) + 1 + ε - 8 / 3) := by
    have htend : Tendsto (fun i => (regime.B i) ^ ((k : ℝ) + 1 + ε - 8 / 3)) atTop atTop :=
      (tendsto_rpow_atTop hgap_plane).comp regime.B_tendsto
    exact htend.eventually (eventually_ge_atTop Cplane)
  filter_upwards [hevM, hevCard, hevB1, hevLine, hevPlane] with i hM hCard hB1 hLine hPlane
  intro Ff hFf
  -- The pool piece in the flat and its real span.
  set Sfin : Finset (RPoint d) :=
    (TrackD.poolPts (T.sources i)).filter (fun q => TrackD.toC q ∈ Ff) with hSfin
  set Pglob : Finset (RPoint d) := regime.P i with hPglob
  set H : AffineSubspace ℝ (RPoint d) := affineSpan ℝ (↑Sfin : Set (RPoint d)) with hH
  set u : ℕ := Module.finrank ℝ H.direction with hu
  have hSsub : Sfin ⊆ Pglob := by
    intro q hq
    have hqpool : q ∈ TrackD.poolPts (T.sources i) := (Finset.mem_filter.mp hq).1
    have hpool := mo_pool_subset_global T i hqpool
    -- `poolPts ⊆ P` gives membership; `Pt`/`RPoint` definitionally equal
    simpa [hPglob] using hpool
  have hSmemH : ∀ q ∈ Sfin, q ∈ H := by
    intro q hq
    have hqset : q ∈ (↑Sfin : Set (RPoint d)) := Finset.mem_coe.mpr hq
    exact mem_affineSpan ℝ hqset
  have hS_le_Pcap : Sfin.card ≤ (Pglob.filter (· ∈ H)).card := by
    apply Finset.card_le_card
    intro q hq
    exact Finset.mem_filter.mpr ⟨hSsub hq, hSmemH q hq⟩
  -- Real dimension bounded by the complex dimension.
  have hu_le : u ≤ k + 1 := by
    have hmem : ∀ q ∈ Sfin, cplx q ∈ Ff := by
      intro q hq
      have hqF : TrackD.toC q ∈ Ff := (Finset.mem_filter.mp hq).2
      exact hqF
    have hdim := mo_affine_dim_le Sfin Ff hmem
    -- `H.direction` is exactly the affine span's direction
    simpa [hH, hu] using hdim.trans hFf
  -- Rewrite scales to the global configuration.
  have hBpos : 0 < regime.B i := regime.B_pos i
  have hBnonneg : 0 ≤ regime.B i := hBpos.le
  have hAeq : regime.A i = (regime.B i) ^ (2 : ℕ) := by
    rw [regime.A_eq_B_sq]
  -- `Mcount Pglob = regime.M i`, `Ascale/Bscale` vs `A/B`.
  have hMcount_eq : Mcount Pglob = regime.M i := by
    simp [Mcount, Regime.M, hPglob, add_comm]
  have hAscale_eq : Ascale d Pglob.card = regime.A i := by
    simp [Ascale, Regime.A, Regime.N, hPglob]
  have hBscale_eq : Bscale d Pglob.card = regime.B i := by
    simp [Bscale, Regime.B, Regime.N, hPglob]
  have hMleA : Mcount Pglob ≤ Ascale d Pglob.card := by
    rw [hMcount_eq, hAscale_eq]
    exact hM
  have hN0le : Nmax ≤ Pglob.card := by simpa [hPglob] using hCard
  -- Target RHS in rpow form.
  have hexp_eq : Real.exp (ε * M.s i) = (regime.B i) ^ ε := by
    rw [hs i, mul_comm, ← Real.rpow_def_of_pos hBpos]
  have hRHS_eq : (regime.B i) ^ (k + 1) * Real.exp (ε * M.s i)
      = (regime.B i) ^ ((k + 1 : ℝ) + ε) := by
    rw [hexp_eq, ← Real.rpow_natCast, ← Real.rpow_add hBpos]
    congr 1
    push_cast
    ring
  rw [hRHS_eq]
  -- Split by `u`.
  by_cases hu0 : u ≤ 1
  · -- Line cap: `|P ∩ H| ≤ 2M-1 ≤ 2A = 2B² ≤ B^{k+1+ε}`.
    have hHle : Module.finrank ℝ H.direction ≤ 1 := hu ▸ hu0
    have hcap := Reduction.card_inter_line_le Pglob H hHle
    have hSle : (Sfin.card : ℝ) ≤ ((Pglob.filter (· ∈ H)).card : ℝ) :=
      by exact_mod_cast hS_le_Pcap
    have hMcount_le_A : Mcount Pglob ≤ regime.A i := by
      rw [hMcount_eq]
      exact hM
    have hMle : ((Pglob.filter (· ∈ H)).card : ℝ) ≤ 2 * regime.A i := by
      have hcapM : ((Pglob.filter (· ∈ H)).card : ℝ) ≤ 2 * Mcount Pglob - 1 := hcap
      linarith
    have hA_rpow : regime.A i = (regime.B i) ^ (2 : ℝ) := by
      rw [hAeq]
      simp
    have hB2_nonneg : (0 : ℝ) ≤ (regime.B i) ^ (2 : ℝ) :=
      Real.rpow_nonneg hBnonneg _
    have hexp_split : ((k + 1 : ℝ) + ε) = 2 + ((k : ℝ) - 1 + ε) := by
      ring
    have hBpow_split : (regime.B i) ^ ((k + 1 : ℝ) + ε)
        = (regime.B i) ^ (2 : ℝ) * (regime.B i) ^ ((k : ℝ) - 1 + ε) := by
      rw [hexp_split, Real.rpow_add hBpos]
    rw [hBpow_split]
    calc (Sfin.card : ℝ)
        ≤ ((Pglob.filter (· ∈ H)).card : ℝ) := hSle
      _ ≤ 2 * regime.A i := hMle
      _ = 2 * (regime.B i) ^ (2 : ℝ) := by rw [hA_rpow]
      _ = (regime.B i) ^ (2 : ℝ) * 2 := by ring
      _ ≤ (regime.B i) ^ (2 : ℝ) * (regime.B i) ^ ((k : ℝ) - 1 + ε) :=
          mul_le_mul_of_nonneg_left hLine hB2_nonneg
  · have hu0lt : 1 < u := not_le.mp hu0
    by_cases hu2 : u = 2
    · -- Plane cap: `|P ∩ H| ≤ C M^{4/3} ≤ C B^{8/3} ≤ B^{k+1+ε}` (needs `k ≥ 2`).
      have hH2 : Module.finrank ℝ H.direction = 2 := hu ▸ hu2
      have hcap := hplane Pglob H hH2
      have hSle : (Sfin.card : ℝ) ≤ ((Pglob.filter (· ∈ H)).card : ℝ) :=
        by exact_mod_cast hS_le_Pcap
      have hMnonneg : (0 : ℝ) ≤ Mcount Pglob := by
        unfold Mcount
        positivity
      have hMleA' : Mcount Pglob ≤ regime.A i := by
        rw [hMcount_eq]
        exact hM
      have hA_nonneg : (0 : ℝ) ≤ regime.A i := le_trans hMnonneg hMleA'
      have hMpow_le : Mcount Pglob ^ ((4 : ℝ) / 3) ≤ regime.A i ^ ((4 : ℝ) / 3) :=
        Real.rpow_le_rpow hMnonneg hMleA' (by norm_num)
      have hA_rpow2 : regime.A i ^ ((4 : ℝ) / 3) = (regime.B i) ^ ((8 : ℝ) / 3) := by
        have hA2 : regime.A i = (regime.B i) ^ (2 : ℝ) := by
          rw [hAeq]
          simp
        rw [hA2, ← Real.rpow_mul hBnonneg]
        congr 1
        norm_num
      have hB83_nonneg : (0 : ℝ) ≤ (regime.B i) ^ ((8 : ℝ) / 3) :=
        Real.rpow_nonneg hBnonneg _
      have hexp_split_plane : ((k + 1 : ℝ) + ε) = 8 / 3 + ((k : ℝ) + 1 + ε - 8 / 3) := by
        ring
      have hBpow_split_plane : (regime.B i) ^ ((k + 1 : ℝ) + ε)
          = (regime.B i) ^ ((8 : ℝ) / 3) * (regime.B i) ^ ((k : ℝ) + 1 + ε - 8 / 3) := by
        conv_lhs => rw [hexp_split_plane]
        rw [Real.rpow_add hBpos]
      rw [hBpow_split_plane]
      calc (Sfin.card : ℝ)
          ≤ ((Pglob.filter (· ∈ H)).card : ℝ) := hSle
        _ ≤ Cplane * Mcount Pglob ^ ((4 : ℝ) / 3) := hcap
        _ ≤ Cplane * (regime.A i ^ ((4 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_left hMpow_le hCplane.le
        _ = Cplane * (regime.B i) ^ ((8 : ℝ) / 3) := by rw [hA_rpow2]
        _ ≤ (regime.B i) ^ ((k : ℝ) + 1 + ε - 8 / 3) * (regime.B i) ^ ((8 : ℝ) / 3) := by
            apply mul_le_mul_of_nonneg_right hPlane hB83_nonneg
        _ = (regime.B i) ^ ((8 : ℝ) / 3) * (regime.B i) ^ ((k : ℝ) + 1 + ε - 8 / 3) := by
            ring
    · have hu3 : 3 ≤ u := by omega
      have hud : u < d := lt_of_le_of_lt hu_le hkd
      have hult : u < k + 2 := by omega
      have hN0u_le : N0 u hu3 hud ≤ Pglob.card :=
        le_trans (hNmax_ge u hu3 hud hult) hN0le
      have hHu_eq : Module.finrank ℝ H.direction = u := hu.symm
      have hcap := hN0 u hu3 hud Pglob hN0u_le hMleA H hHu_eq
      have hSle : (Sfin.card : ℝ) ≤ ((Pglob.filter (· ∈ H)).card : ℝ) :=
        by exact_mod_cast hS_le_Pcap
      have hBcap : ((Pglob.filter (· ∈ H)).card : ℝ)
          ≤ (regime.B i) ^ (((u : ℝ)) + ε) := by
        have hcapB : ((Pglob.filter (· ∈ H)).card : ℝ)
            ≤ Bscale d Pglob.card ^ (((u : ℝ)) + ε) := hcap
        rwa [hBscale_eq] at hcapB
      have hexp_le : ((u : ℝ) + ε) ≤ ((k + 1 : ℝ) + ε) := by
        have hu_le_r : (u : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hu_le
        have hkcast : (((k + 1 : ℕ)) : ℝ) = ((k : ℝ) + 1) := by push_cast; ring
        rw [hkcast] at hu_le_r
        have hgoal : ((u : ℝ) + ε) ≤ ((k : ℝ) + 1 + ε) := by linarith
        simpa using hgoal
      have hBpow_le : (regime.B i) ^ (((u : ℝ)) + ε)
          ≤ (regime.B i) ^ ((k + 1 : ℝ) + ε) :=
        Real.rpow_le_rpow_of_exponent_le hB1 hexp_le
      calc (Sfin.card : ℝ)
          ≤ ((Pglob.filter (· ∈ H)).card : ℝ) := hSle
        _ ≤ (regime.B i) ^ (((u : ℝ)) + ε) := hBcap
        _ ≤ (regime.B i) ^ ((k + 1 : ℝ) + ε) := hBpow_le

end
end DistinctDistances.SparseCones
