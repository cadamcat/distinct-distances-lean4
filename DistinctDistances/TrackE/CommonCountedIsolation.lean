import DistinctDistances.TrackE.CommonSectionInputs

/-! Each counted actual label is isolated in the WHOLE original intersection,
`sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_counted_label_isolated {d k : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (hZ : (commonProductImage i₀ X Y).IsIrreducible)
    (φ ψ : AffineProjection d k) (E : Fin (2 * k) → Poly (d + d))
    (hlin : ∀ i, (E i).totalDegree ≤ 1) (p v : Point d) (hp : p ∈ X)
    (hlift : ∃ y ∈ Y, commonTangentPair i₀ X Y p y ∧
      TrackD.dirChart (LinearMap.proj i₀) (y - p) = v)
    (hsource : Function.Injective (φ.linear.domRestrict (X.tangentSpace p)))
    (hdirection : Function.Injective (ψ.linear.domRestrict
      ((TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)).tangentSpace v)))
    (hzero : ∀ i, MvPolynomial.eval (TrackD.productPoint p v) (E i) = 0)
    (hkernel : LinearMap.ker (LinearMap.pi (fun i => differential (E i)
      (TrackD.productPoint p v))) = LinearMap.ker (commonBlockLinearMap φ.linear ψ.linear)) :
    pointIdeal (TrackD.productPoint p v) ∈
      ((commonProductImage i₀ X Y).ideal ⊔ Ideal.span (Set.range E)).minimalPrimes := by
  obtain ⟨y, hy, hpair, hdir⟩ := hlift
  subst v
  have hz : TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p)) ∈
      commonProductImage i₀ X Y := common_product_label_mem i₀ X Y p y hp hy hpair.1
  have hblock := common_label_block_tangent_injective (d := d) (k := k)
    i₀ X Y p y hp hy hpair φ.linear ψ.linear hsource hdirection
  have hinj : Function.Injective ((LinearMap.pi (fun i => differential (E i)
      (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p))))).domRestrict
        ((commonProductImage i₀ X Y).tangentSpace
          (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p))))) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have hmem : w.val ∈ LinearMap.ker (LinearMap.pi (fun i => differential (E i)
        (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p))))) := hw
    have hb := (SetLike.ext_iff.mp hkernel w.val).mp hmem
    apply hblock
    simpa only [LinearMap.domRestrict_apply, map_zero, LinearMap.mem_ker] using hb
  exact Request.common_linear_section_isolated (commonProductImage i₀ X Y) hZ E hlin
    (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p))) hz hzero hinj

end
end DistinctDistances.SparseCones
