import DistinctDistances.TrackE.CommonTangentOpens

/-! The SAME source and direction equations kill the full original image
tangent at counted labels, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_label_block_tangent_injective {d k : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (p y : Point d) (hp : p ∈ X) (hy : y ∈ Y)
    (hpair : commonTangentPair i₀ X Y p y) (φ ψ : LinearProjection d k)
    (hsource : Function.Injective (φ.domRestrict (X.tangentSpace p)))
    (hdirection : Function.Injective (ψ.domRestrict
      ((TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)).tangentSpace
        (TrackD.dirChart (LinearMap.proj i₀) (y - p))))) :
    Function.Injective ((commonBlockLinearMap φ ψ).domRestrict
      ((commonProductImage i₀ X Y).tangentSpace
        (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p))))) := by
  have hmap : (commonProductImage i₀ X Y).tangentSpace
      (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p))) =
      ((X.tangentSpace p).prod (Y.tangentSpace y)).map
        ((TrackD.productLinearEquiv (d := d)).toLinearMap.comp
          (TrackD.labelDeriv (LinearMap.proj i₀) p y)) := by
    rw [Submodule.map_comp]
    exact hpair.2.1.symm.trans (TrackD.rational_secant_tangent_map X Y i₀ p y hp hy hpair.1)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hzero
  change commonBlockLinearMap φ ψ (w : Point (d + d)) = 0 at hzero
  have hw := (SetLike.ext_iff.mp hmap w.val).mp w.property
  obtain ⟨a, ha, hae⟩ := Submodule.mem_map.mp hw
  rw [← hae] at hzero
  change commonBlockLinearMap φ ψ (TrackD.productPoint
    (TrackD.labelDeriv (LinearMap.proj i₀) p y a).1
    (TrackD.labelDeriv (LinearMap.proj i₀) p y a).2) = 0 at hzero
  rw [common_block_linear_map_product] at hzero
  change (TrackD.productLinearEquiv (d := k))
    (φ (TrackD.labelDeriv (LinearMap.proj i₀) p y a).1,
      ψ (TrackD.labelDeriv (LinearMap.proj i₀) p y a).2) = 0 at hzero
  have hb := congrArg (TrackD.productLinearEquiv (d := k)).symm hzero
  simp only [LinearEquiv.symm_apply_apply, map_zero] at hb
  have hξsub : (⟨a.1, ha.1⟩ : X.tangentSpace p) = 0 := by
    apply hsource
    simpa [TrackD.labelDeriv] using congrArg Prod.fst hb
  have hξ : a.1 = 0 := congrArg Subtype.val hξsub
  let v := TrackD.dirChartDeriv (LinearMap.proj i₀) (y - p) a.2
  have hv : v ∈ (TrackA.projectiveLinearSlice (radialImage p Y)
      (MvPolynomial.X i₀)).tangentSpace (TrackD.dirChart (LinearMap.proj i₀) (y - p)) := by
    rw [← hpair.2.2]
    exact Submodule.mem_map.mpr ⟨a.2, ha.2, rfl⟩
  have hvsub : (⟨v, hv⟩ : (TrackA.projectiveLinearSlice (radialImage p Y)
      (MvPolynomial.X i₀)).tangentSpace (TrackD.dirChart (LinearMap.proj i₀) (y - p))) = 0 := by
    apply hdirection
    simpa [TrackD.labelDeriv, hξ, v] using congrArg Prod.snd hb
  have hvzero : v = 0 := congrArg Subtype.val hvsub
  have hl : TrackD.labelDeriv (LinearMap.proj i₀) p y a = 0 := by
    apply Prod.ext
    · simpa [TrackD.labelDeriv] using hξ
    · simpa [TrackD.labelDeriv, hξ, v] using hvzero
  apply Subtype.ext
  change (w : Point (d + d)) = 0
  rw [← hae]
  change (TrackD.productLinearEquiv (d := d)).toLinearMap
    (TrackD.labelDeriv (LinearMap.proj i₀) p y a) = 0
  rw [hl, map_zero]

end
end DistinctDistances.SparseCones
