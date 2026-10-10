import DistinctDistances.TrackD.SecantsImageGeometry
import DistinctDistances.TrackD.SecantsChart
import DistinctDistances.TrackD.Inputs
import DistinctDistances.TrackD.SecantsSpan
import DistinctDistances.TrackD.Requests
import DistinctDistances.TrackD.FunctionFieldConstancy
import DistinctDistances.TrackD.GenericCotangent
import DistinctDistances.TrackD.SecantsRank

/-!
# `geo:secants` (`secants.tex:25–103`)

The secant tangent calculation and its particular-pair version. Varieties are reduced complex
affine varieties of the shared model; tangent spaces are Zariski tangent spaces
(`AffineVariety.tangentSpace`), which agree with the geometric ones at general points.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

variable {d : ℕ}

/-- `geo:secants.zero-diff` (`secants.tex:89–95`). Characteristic zero: a rational function
`a/b` on an irreducible variety whose differential vanishes on the tangent spaces at general
points is constant. The hypothesis is the numerator of `d(a/b)`. -/
theorem geo_secants_zero_diff (X : AffineVariety d) (hX : X.IsIrreducible) (a b : Poly d)
    (hb : ∃ x ∈ X, MvPolynomial.eval x b ≠ 0)
    (h : ForGeneralPoint X (fun x => ∀ v ∈ X.tangentSpace x,
      MvPolynomial.eval x b * differential a x v - MvPolynomial.eval x a * differential b x v = 0)) :
    ∃ c : ℂ, ∀ x ∈ X, MvPolynomial.eval x a = c * MvPolynomial.eval x b := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  let φ := coordinateFieldMap X.ideal K
  have hker : RingHom.ker φ = X.ideal := coordinateFieldMap_kernel X.ideal K
  letI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ R K
  exact polynomial_ratio_constancy X K φ hker a b hb
    (generic_tangent_differential X hX K a b h)

/-- The non-tangency hypothesis of `geo:secants`: at a general pair the connecting direction is
in neither tangent space. -/
def GenericallyTransverse (X Y : AffineVariety d) : Prop :=
  ForGeneralPair X Y (fun x y => y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y)

/-- `geo:secants`, equal projected tangents (`secants.tex:32–35`, proof 83–102). For `k = l`,
equality of the projected tangent spaces at a general transverse pair puts `X, Y` in a common
affine `(k+1)`-flat. -/
theorem geo_secants_equal_tangents (X Y : AffineVariety d) (k : ℕ)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hk : X.dimension = k) (hl : Y.dimension = k) (hk1 : 1 ≤ k)
    (htr : GenericallyTransverse X Y)
    (heq : ForGeneralPair X Y (fun x y =>
      X.tangentSpace x ⊔ (ℂ ∙ (y - x)) = Y.tangentSpace y ⊔ (ℂ ∙ (y - x)))) :
    ∃ F : AffineSubspace ℂ (Point d),
      Module.finrank ℂ F.direction ≤ k + 1 ∧ X.points ⊆ F ∧ Y.points ⊆ F := by
  exact common_flat_of_equal_tangents
    (fun V hV a b hb h => geo_secants_zero_diff V hV a b hb h) X Y k hX hY
    (by simpa only [hk] using request_general_tangent_finrank X hX)
    (by simpa only [hl] using request_general_tangent_finrank Y hY) heq

/-! ### The particular-pair assertion (`secants.tex:37–54`, proof 57–81)

The label map `ψ(x, y) = (x, π_x y)` in the direction chart `{λ ≠ 0}` of `ℙ^{d-1}`, where
`λ` is a linear functional: `π_x y` is represented by `φ(y - x)` with `φ(u) = u / λ(u)`. -/

/-- `geo:secants.local-deriv`: `labelDeriv` is the Fréchet derivative of the label map in the
chart, wherever `λ(y - x) ≠ 0`. -/
theorem labelDeriv_hasFDerivAt (lam : Point d →ₗ[ℂ] ℂ) (x y : Point d) (h : lam (y - x) ≠ 0) :
    HasFDerivAt (fun z : Point d × Point d => (z.1, dirChart lam (z.2 - z.1)))
      (LinearMap.toContinuousLinearMap (labelDeriv lam x y)) (x, y) := by
  have hchart : HasFDerivAt (fun u : Point d => dirChart lam u)
      (LinearMap.toContinuousLinearMap (dirChartDeriv lam (y - x))) (y - x) := by
    have hlam : HasFDerivAt (fun u : Point d => lam u) lam.toContinuousLinearMap (y - x) :=
      lam.toContinuousLinearMap.hasFDerivAt
    have hinv := (hasFDerivAt_inv h).comp (y - x) hlam
    have hid : HasFDerivAt (fun u : Point d => u)
        (ContinuousLinearMap.id ℂ (Point d)) (y - x) := by
      exact hasFDerivAt_id (𝕜 := ℂ) (y - x)
    have hsmul := hinv.smul hid
    convert hsmul using 1
    · ext u
      simp [dirChart]
    · ext v
      simp [dirChartDeriv, LinearMap.smulRight_apply, smul_smul]
      ring
  have hsub : HasFDerivAt (fun z : Point d × Point d => z.2 - z.1)
      (LinearMap.toContinuousLinearMap
        (LinearMap.snd ℂ (Point d) (Point d) - LinearMap.fst ℂ (Point d) (Point d))) (x, y) := by
    exact (LinearMap.toContinuousLinearMap
      (LinearMap.snd ℂ (Point d) (Point d) - LinearMap.fst ℂ (Point d) (Point d))).hasFDerivAt
  have hsecond := hchart.comp (x, y) hsub
  have hfst : HasFDerivAt (fun z : Point d × Point d => z.1)
      (LinearMap.toContinuousLinearMap (LinearMap.fst ℂ (Point d) (Point d))) (x, y) := by
    exact (LinearMap.toContinuousLinearMap (LinearMap.fst ℂ (Point d) (Point d))).hasFDerivAt
  have hpair := hfst.prodMk hsecond
  have hD : LinearMap.toContinuousLinearMap (labelDeriv lam x y) =
      (LinearMap.toContinuousLinearMap (LinearMap.fst ℂ (Point d) (Point d))).prod
        (LinearMap.toContinuousLinearMap (dirChartDeriv lam (y - x)) ∘L
          LinearMap.toContinuousLinearMap
            (LinearMap.snd ℂ (Point d) (Point d) - LinearMap.fst ℂ (Point d) (Point d))) := by
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · simp [labelDeriv]
    · simp [labelDeriv]
  rw [hD]
  simpa [Function.comp_def, id] using hpair

/-- `geo:secants.local` (`secants.tex:37–54`, eq. `geo:tangent-inclusion`), tangent-level form.
`TX, TY` are the tangent spaces of `X` at `p` and of `Y` at `q`; `TW` is the tangent space of a
smooth local variety `W` of dimension `dim TX + dim TY` at the common label `ψ(p,q) = ψ(p,z)`.
If the differential of `ψ` at `(p,q)` maps `TX × TY` into `TW` with full rank, and source
variation at `(p, z)` (the other root, `z - p = c (q - p)`, `c ≠ 0, 1`) also stays in `TW`, then
`TX ⊆ TY + ℂ(q - p)`. The analytic hypotheses of the paper (images of `X × Y` and `X × Y'` lie in
`W` near the relevant pairs) give `hqW` and `hzW` by the chain rule. -/
theorem geo_secants_local (lam : Point d →ₗ[ℂ] ℂ) (p q z : Point d) (c : ℂ)
    (hlam : lam (q - p) ≠ 0) (hz : z - p = c • (q - p)) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (TX TY : Submodule ℂ (Point d)) (TW : Submodule ℂ (Point d × Point d))
    (hqW : (TX.prod TY).map (labelDeriv lam p q) ≤ TW)
    (hrank : Module.finrank ℂ ((TX.prod TY).map (labelDeriv lam p q)) =
      Module.finrank ℂ TX + Module.finrank ℂ TY)
    (hdimW : Module.finrank ℂ TW = Module.finrank ℂ TX + Module.finrank ℂ TY)
    (hzW : (TX.prod (⊥ : Submodule ℂ (Point d))).map (labelDeriv lam p z) ≤ TW) :
    TX ≤ TY ⊔ (ℂ ∙ (q - p)) := by
  let u := q - p
  have hlu : lam u ≠ 0 := by simpa [u] using hlam
  have hscale : dirChartDeriv lam (c • u) = c⁻¹ • dirChartDeriv lam u := by
    ext v
    simp [dirChartDeriv, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul]
    field_simp [hlu, hc0]
  have hqform (ξ η : Point d) :
      labelDeriv lam p q (ξ, η) = (ξ, dirChartDeriv lam u (η - ξ)) := by
    simp [labelDeriv, u]
  have hzform (ξ η : Point d) :
      labelDeriv lam p z (ξ, η) = (ξ, dirChartDeriv lam (c • u) (η - ξ)) := by
    simp [labelDeriv, u, hz]
  let S := (TX.prod TY).map (labelDeriv lam p q)
  have hSeq : S = TW := by
    apply Submodule.eq_of_le_of_finrank_eq hqW
    exact hrank.trans hdimW.symm
  intro ξ hξ
  let a : ℂ := 1 - c⁻¹
  have ha : a ≠ 0 := by
    dsimp [a]
    intro h
    apply hc1
    have hi : c⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have : c = 1 := by
      calc
        c = c * 1 := by simp
        _ = c * c⁻¹ := by rw [hi]
        _ = 1 := mul_inv_cancel₀ hc0
    exact this
  have hqmem : labelDeriv lam p q (ξ, 0) ∈ S := by
    change labelDeriv lam p q (ξ, 0) ∈ (TX.prod TY).map (labelDeriv lam p q)
    rw [Submodule.mem_map]
    refine ⟨(ξ, 0), ?_, rfl⟩
    simp [hξ]
  have hzmem : labelDeriv lam p z (ξ, 0) ∈
      (TX.prod (⊥ : Submodule ℂ (Point d))).map (labelDeriv lam p z) := by
    rw [Submodule.mem_map]
    refine ⟨(ξ, 0), ?_, rfl⟩
    simp [hξ]
  have hqTW : labelDeriv lam p q (ξ, 0) ∈ TW := hqW hqmem
  have hzTW : labelDeriv lam p z (ξ, 0) ∈ TW := hzW hzmem
  have hdiff : (0, a • dirChartDeriv lam u ξ) ∈ TW := by
    have hEq : (0, a • dirChartDeriv lam u ξ) =
        labelDeriv lam p z (ξ, 0) - labelDeriv lam p q (ξ, 0) := by
      rw [hzform, hqform, hscale]
      dsimp [a]
      simp [map_neg]
      module
    rw [hEq]
    exact TW.sub_mem hzTW hqTW
  have hdiffS : (0, a • dirChartDeriv lam u ξ) ∈ S := by
    exact hSeq.symm ▸ hdiff
  obtain ⟨⟨ξ', η⟩, hxy, heq⟩ := (Submodule.mem_map.mp hdiffS)
  have hξ' : ξ' = 0 := by
    have := congrArg Prod.fst heq
    simpa [labelDeriv] using this
  have hη : η ∈ TY := by
    simpa using hxy.2
  have hmapval : dirChartDeriv lam u η = a • dirChartDeriv lam u ξ := by
    have := congrArg Prod.snd heq
    simpa [labelDeriv, hξ'] using this
  have hker : dirChartDeriv lam u (η - a • ξ) = 0 := by
    rw [map_sub, map_smul, hmapval]
    simp
  have hker_mem : η - a • ξ ∈ ℂ ∙ u := by
    rw [Submodule.mem_span_singleton]
    have hform : (lam u)⁻¹ • (η - a • ξ) -
        (((lam u) ^ 2)⁻¹ * lam (η - a • ξ)) • u = 0 := by
      simpa [dirChartDeriv, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.smulRight_apply, smul_smul] using hker
    refine ⟨(lam u)⁻¹ * lam (η - a • ξ), ?_⟩
    symm
    have hform' := sub_eq_zero.mp hform
    have hcoeff : lam u * (((lam u) ^ 2)⁻¹ * lam (η - a • ξ)) =
        (lam u)⁻¹ * lam (η - a • ξ) := by
      field_simp [hlu]
    calc
      η - a • ξ = lam u • ((lam u)⁻¹ • (η - a • ξ)) := by simp [hlu]
      _ = lam u • ((((lam u) ^ 2)⁻¹ * lam (η - a • ξ)) • u) := by rw [hform']
      _ = (lam u * (((lam u) ^ 2)⁻¹ * lam (η - a • ξ))) • u := by rw [smul_smul]
      _ = ((lam u)⁻¹ * lam (η - a • ξ)) • u := by rw [hcoeff]
  let W : Submodule ℂ (Point d) := TY ⊔ (ℂ ∙ u)
  have hasum : a • ξ ∈ W := by
    have hηW : η ∈ W := Submodule.mem_sup_left hη
    have hkW : η - a • ξ ∈ W := Submodule.mem_sup_right hker_mem
    have hx := W.sub_mem hηW hkW
    simpa [W, sub_sub_cancel] using hx
  have hξW : ξ ∈ W := by
    have hx := W.smul_mem a⁻¹ hasum
    simpa [W, smul_smul, ha] using hx
  simpa [W, u] using hξW

/-- `geo:secants`, further-root part (`secants.tex:25–32`, proof 57–102). Irreducible `X, Y, Y'`
of dimensions `k, l, l ≥ 1`; at a general pair of `X × Y` the connecting direction is
transverse to both tangents, and the connecting line has a further point of `Y'` other than
`x, y`. Then `k ≤ l`, and if `k = l` then `X` and `Y` lie in a common affine `(k+1)`-flat. -/
theorem geo_secants_further_root (X Y Y' : AffineVariety d) (k l : ℕ)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) (hY' : Y'.IsIrreducible)
    (hk : X.dimension = k) (hl : Y.dimension = l) (hl' : Y'.dimension = l)
    (hk1 : 1 ≤ k) (hl1 : 1 ≤ l) (htr : GenericallyTransverse X Y)
    (hroot : ForGeneralPair X Y (fun x y =>
      ∃ z ∈ Y', z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z - x = c • (y - x))) :
    k ≤ l ∧ (k = l → ∃ F : AffineSubspace ℂ (Point d),
      Module.finrank ℂ F.direction ≤ k + 1 ∧ X.points ⊆ F ∧ Y.points ⊆ F) := by
  obtain ⟨i, hlabels⟩ := further_root_label_tangents X Y Y' hX hY hY'
    (hl'.trans hl.symm) (by omega) htr hroot
  have hinc : ForGeneralPair X Y (fun x y =>
      X.tangentSpace x ≤ Y.tangentSpace y ⊔ (ℂ ∙ (y - x))) := by
    apply (hlabels.and hX hY htr).mono
    intro x hx y hy hh
    rcases hh with ⟨⟨z, hz, c, hc0, hc1, hline, hi, hzW⟩, htrans⟩
    let TW := ((X.tangentSpace x).prod (Y.tangentSpace y)).map
      (labelDeriv (LinearMap.proj i) x y)
    have hrank := labelDeriv_product_finrank (LinearMap.proj i) x y hi
      (X.tangentSpace x) (Y.tangentSpace y) htrans.2
    exact geo_secants_local (LinearMap.proj i) x y z c hi hline hc0 hc1
      (X.tangentSpace x) (Y.tangentSpace y) TW (le_refl _) hrank hrank hzW
  obtain ⟨hkl, heq⟩ := generic_secant_rank X Y k l hX hY hk hl htr hinc
  refine ⟨hkl, ?_⟩
  intro hEq
  exact geo_secants_equal_tangents X Y k hX hY hk (hl.trans hEq.symm) hk1 htr (heq hEq)


end

end TrackD
end DistinctDistances
