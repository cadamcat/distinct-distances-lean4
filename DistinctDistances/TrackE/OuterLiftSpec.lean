import DistinctDistances.TrackE.OuterRegularity
import DistinctDistances.TrackE.OuterLiftCurve
import DistinctDistances.TrackE.CommonImageInputs
import DistinctDistances.TrackD.ProductTangents

/-! The specialized label equations at the source point (sparse-cones.tex:580–594).

At a fixed source `p` the common label equations `G(x, w)` specialize to
`G(p, w)` (`outerSpecEq`). They vanish on the chart directions `φ(y)` of the
target carrier (`outer_spec_vanish`, from `hvanish`), and the per-pair tangent
data give injectivity of `dφ_q` on `T_qY` and a Jacobian kernel of rank `≤ k`
at `w₀ = φ(q)` (`outer_spec_tangent`). These are the hypotheses `h1`–`h3` of
`outer_curve_from_jets`. -/
namespace DistinctDistances.SparseCones
open MvPolynomial
open scoped Classical
noncomputable section
variable {d : ℕ}

/-- The label equation `G(x, w)` specialized at the source `x = p`, as a
polynomial in the direction chart coordinates `w`. -/
def outerSpecEq (p : Point d) (G : TrackD.PairPoly d) : Poly d :=
  aeval (Sum.elim (fun a => C (p a)) X) G

theorem outerSpecEq_eval (p w : Point d) (G : TrackD.PairPoly d) :
    eval w (outerSpecEq p G) = eval (TrackD.pairPt p w) G := by
  unfold outerSpecEq
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | mul_X f i hf =>
    rw [map_mul, map_mul, hf, map_mul]
    cases i <;> simp [TrackD.pairPt]

/-- sc:outer-lift.spec-vanish . `eval w (outerSpecEq p G) =
eval (pairPt p w) G`; for `y ∈ Y` off the chart hyperplane, `(p, φ(y))` read in
`Fin (d + d)` is the rational label point of `productPoint p y` (in
`productVariety X Y` by `subset_closure`, denominator `(y - p)_{i₀} ≠ 0`), so it
lies in `commonProductImage i₀ X Y` (`TrackD.rationalPoint_mem_image`), where
`commonPairEquation G` vanishes (`hvanish`; `rename finSumFinEquiv` evaluation). -/
theorem outer_spec_vanish (i₀ : Fin d) (p : Point d) (X Y : AffineVariety d)
    (hpX : p ∈ X.points) (Eqs : Finset (TrackD.PairPoly d))
    (hvanish : ∀ G ∈ Eqs,
      commonPairEquation G ∈ (commonProductImage i₀ X Y).ideal) :
    ∀ y ∈ Y.points, (y - p) i₀ ≠ 0 → ∀ e ∈ Eqs.image (outerSpecEq p),
      eval (((y - p) i₀)⁻¹ • (y - p)) e = 0 := by
  intro y hy hi e he
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp he
  have hmem : commonPairEquation G ∈ (commonProductImage i₀ X Y).ideal :=
    hvanish G hG
  have hlabel : MvPolynomial.eval (TrackD.labelPt i₀ p y) G = 0 := by
    have h := (common_product_image_equation_iff i₀ X Y G).mp hmem p hpX y hy hi
    exact h
  have hpt : TrackD.labelPt i₀ p y = TrackD.pairPt p (((y - p) i₀)⁻¹ • (y - p)) := rfl
  rw [outerSpecEq_eval]
  rw [← hpt]
  exact hlabel

/-- `outerSpecEq` is the left partial evaluation `pairFixLeft`. -/
theorem outerSpecEq_eq_pairFixLeft (p : Point d) (G : TrackD.PairPoly d) :
    outerSpecEq p G = TrackD.pairFixLeft G p := rfl

/-- Renaming back from shared coordinates recovers the pair polynomial. -/
theorem rename_symm_commonPair (G : TrackD.PairPoly d) :
    MvPolynomial.rename finSumFinEquiv.symm (commonPairEquation G) = G := by
  simp [commonPairEquation]

/-- The label derivative on a pair `(a, v)`. -/
theorem labelDeriv_apply (lam : Point d →ₗ[ℂ] ℂ) (x y : Point d)
    (a v : Point d) :
    TrackD.labelDeriv lam x y (a, v) =
      (a, TrackD.dirChartDeriv lam (y - x) (v - a)) := by
  simp [TrackD.labelDeriv]

/-- Differential of the specialized equation equals the differential of the
shared-coordinate equation along `outerPairLinear (0, ·)`. -/
theorem differential_outerSpecEq (p w : Point d) (G : TrackD.PairPoly d)
    (b : Point d) :
    differential (outerSpecEq p G) w b =
      differential (commonPairEquation G) (TrackD.productPoint p w)
        (outerPairLinear (0, b)) := by
  have hOuter : outerPairLinear (0, b) = TrackD.productPoint 0 b := by
    rw [outerPairLinear_eq_productLinearEquiv]
    rfl
  have hRename : MvPolynomial.rename finSumFinEquiv.symm (commonPairEquation G) = G :=
    rename_symm_commonPair G
  have hFix : TrackD.pairFixLeft G p = outerSpecEq p G := rfl
  have hprod := TrackD.differential_product (commonPairEquation G) p w 0 b
  rw [← hOuter] at hprod
  -- hprod : diff f (pp p w) (outer ..) = diff (fixR ...) p 0 + diff (fixL ...) w b
  rw [hRename] at hprod
  -- fixL G p = outerSpecEq p G
  rw [hFix] at hprod
  have hzero' : differential (TrackD.pairFixRight G w) p (0 : Point d) = 0 :=
    map_zero _
  rw [hzero', zero_add] at hprod
  exact hprod.symm

/-- The shared-coordinate label point is the product point of the chart direction. -/
theorem outerLabelPt_eq (i₀ : Fin d) (p q : Point d) :
    (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) =
      TrackD.productPoint p (((q - p) i₀)⁻¹ • (q - p)) := by
  funext kk
  rfl

/-- sc:outer-lift.spec-tangent . Write
`D = dirChartDeriv (proj i₀) (q - p)`, so `labelDeriv (proj i₀) p q (a, v) =
(a, D (v - a))`. (i) `labelDeriv` is injective on `TX × TY` (`tdata.hrank`:
the image has the full rank `k + k`), so `v ∈ TY = T_qY`, `D v = 0` gives
`(0, v) = 0`. (ii) `d(outerSpecEq p G)_{w₀} b = dG_{(p, w₀)} (0, b)` and
`labelPt i₀ p q = pairPt p w₀`, so `b ∈ jacKer` iff `(0, b) ∈ TW =
outerLabelTangent Eqs i₀ p q`; `TW` equals the image of `TX × TY`
(`tdata.hW`, equal finranks `k + k`), so `(0, b) = (a, D (v - a))` forces
`a = 0`, `b = D v`, `v ∈ TY`: the kernel lies in `TY.map D`, of rank `≤ k`. -/
theorem outer_spec_tangent (i₀ : Fin d) (p q : Point d) (X Y : AffineVariety d)
    (k : ℕ) (Eqs : Finset (TrackD.PairPoly d))
    (tdata : OuterTangentData i₀ p q X Y k (outerLabelTangent Eqs i₀ p q)) :
    (∀ v ∈ Y.tangentSpace q,
      TrackD.dirChartDeriv (LinearMap.proj i₀) (q - p) v = 0 → v = 0) ∧
    Module.finrank ℂ (TrackD.jacKer (Eqs.image (outerSpecEq p))
      (((q - p) i₀)⁻¹ • (q - p))) ≤ k := by
  classical
  have hlam : ((LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) (q - p)) ≠ 0 := by
    simpa [LinearMap.proj_apply] using tdata.hchart
  have hinj := TrackD.labelDeriv_injective_on_product
    (LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) p q
    hlam tdata.TX tdata.TY tdata.htgt
  have hpart1 : ∀ v ∈ Y.tangentSpace q,
      TrackD.dirChartDeriv (LinearMap.proj i₀) (q - p) v = 0 → v = 0 := by
    intro v hv hDv
    have hvTY : v ∈ tdata.TY := by rw [tdata.hTY]; exact hv
    have hmem1 : ((0 : Point d), v) ∈ tdata.TX.prod tdata.TY :=
      ⟨Submodule.zero_mem _, hvTY⟩
    have hmem2 : ((0 : Point d), (0 : Point d)) ∈ tdata.TX.prod tdata.TY :=
      ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    have hL1 : TrackD.labelDeriv (LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) p q (0, v) = 0 := by
      rw [labelDeriv_apply]
      simp [hDv]
    have hL2 : TrackD.labelDeriv (LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) p q (0, 0) = 0 := by
      rw [labelDeriv_apply]
      simp
    have hf1 : ((TrackD.labelDeriv (LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) p q).domRestrict
        (tdata.TX.prod tdata.TY)) ⟨(0, v), hmem1⟩ = 0 := by
      simpa using hL1
    have hf2 : ((TrackD.labelDeriv (LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) p q).domRestrict
        (tdata.TX.prod tdata.TY)) ⟨(0, 0), hmem2⟩ = 0 := by
      simpa using hL2
    have heq := hinj (hf1.trans hf2.symm)
    have hval : ((0 : Point d), v) = ((0 : Point d), (0 : Point d)) :=
      congrArg Subtype.val heq
    exact (Prod.mk.injEq ..).mp hval |>.2
  refine ⟨hpart1, ?_⟩
  -- Part (ii): the Jacobian kernel lies in `TY.map D`.
  set w₀ : Point d := (((q - p) i₀)⁻¹ • (q - p)) with hw₀def
  set lam : Point d →ₗ[ℂ] ℂ := (LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) with hlamdef
  set D : Point d →ₗ[ℂ] Point d := TrackD.dirChartDeriv lam (q - p) with hDdef
  set y₀ : Point (d + d) :=
    (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) with hy₀def
  have hy₀eq : y₀ = TrackD.productPoint p w₀ := outerLabelPt_eq i₀ p q
  have hWeq : ((tdata.TX.prod tdata.TY).map
      (TrackD.labelDeriv lam p q)) = outerLabelTangent Eqs i₀ p q := by
    apply Submodule.eq_of_le_of_finrank_eq tdata.hW
    rw [tdata.hrank, tdata.hdimW]
  -- `K ≤ TY.map D`
  have hKle : TrackD.jacKer (Eqs.image (outerSpecEq p)) w₀ ≤
      tdata.TY.map D := by
    intro b hb
    have hbG : ∀ G ∈ Eqs, differential (outerSpecEq p G) w₀ b = 0 := by
      intro G hG
      have he : outerSpecEq p G ∈ Eqs.image (outerSpecEq p) :=
        Finset.mem_image_of_mem _ hG
      have h := hb
      simp only [TrackD.jacKer, Submodule.mem_iInf, LinearMap.mem_ker] at h
      exact h _ he
    -- `(0, b) ∈ TW` via the shared-coordinate kernel
    have hTWmem : ((0 : Point d), b) ∈ outerLabelTangent Eqs i₀ p q := by
      unfold outerLabelTangent
      rw [Submodule.mem_comap]
      rw [outerLabelPt_eq]
      simp only [TrackD.jacKer, Submodule.mem_iInf, LinearMap.mem_ker]
      intro f hf
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hf
      have h0 := hbG G hG
      have hdiff := differential_outerSpecEq p w₀ G b
      rw [hdiff] at h0
      -- h0 : common (pp p w₀) = 0; goal has unfolded w₀
      rw [hw₀def] at h0
      exact h0
    -- transport to the label-derivative image
    have hMapmem : ((0 : Point d), b) ∈
        ((tdata.TX.prod tdata.TY).map (TrackD.labelDeriv lam p q)) := by
      rw [hWeq]
      exact hTWmem
    obtain ⟨⟨a, v⟩, hmem, himg⟩ := Submodule.mem_map.mp hMapmem
    obtain ⟨haTX, hvTY⟩ := hmem
    have hlab : TrackD.labelDeriv lam p q (a, v) = ((0 : Point d), b) := himg
    rw [labelDeriv_apply] at hlab
    have ha0 : a = 0 := (Prod.mk.injEq ..).mp hlab |>.1
    have hDv : D (v - a) = b := (Prod.mk.injEq ..).mp hlab |>.2
    subst ha0
    simp at hDv
    exact Submodule.mem_map.mpr ⟨v, hvTY, hDv⟩
  calc Module.finrank ℂ (TrackD.jacKer (Eqs.image (outerSpecEq p)) w₀)
      ≤ Module.finrank ℂ (tdata.TY.map D) := Submodule.finrank_mono hKle
    _ ≤ Module.finrank ℂ tdata.TY := Submodule.finrank_map_le _ _
    _ = k := tdata.hdimY

end
end DistinctDistances.SparseCones
