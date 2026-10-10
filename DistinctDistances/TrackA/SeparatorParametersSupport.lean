import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPolynomial OAI.PiExponentJets.W22

/-- Original OAI parameter selection gives exactly c bounded equations
and a finite local quotient at an isolated complex or algebraic point. -/
theorem origin_bounded_parameters {F : Type*} [Field F] [IsAlgClosed F]
    (c L : ℕ) (E : Set (FieldPoly c F)) (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (hmin : pointIdealOver (0 : FieldPoint c F) ∈ (Ideal.span E).minimalPrimes) :
    ∃ f : Fin c → FieldPoly c F,
      (∀ i, (f i).totalDegree ≤ L ∧ f i ∈ Ideal.span E) ∧
      Module.length (OriginLocalRing c F)
        (OriginLocalRing c F ⧸ Ideal.span (Set.range
          (fun i => algebraMap (FieldPoly c F) (OriginLocalRing c F) (f i)))) < ⊤ := by
  let P := pointIdealOver (0 : FieldPoint c F)
  let original : E → FieldPoly c F := Subtype.val
  have hrange : Set.range original = E := by ext p; simp [original]
  have hheight : P.height = (c : ℕ∞) := OAI.QuarticPowerFree.mvPolynomial_maximal_height c P
  have hminimal : P ∈ (Ideal.span (Set.range original)).minimalPrimes := by
    rwa [hrange]
  have hrad := localized_radical_eq_maximal_of_mem_minimalPrimes
    (Ideal.span (Set.range original)) P hminimal
  obtain ⟨cs, _, hlen, hdeg, hcontain, _, hgsrad⟩ :=
    OAI.PiExponentSiegel.W58.polynomialLocal_exists_degree_bounded_regular_parameters
      F c P original L c (fun i => hE i.val i.property) hheight hrad
  let gs := cs.map (Finsupp.linearCombination F original)
  change gs.length = c at hlen
  let f : Fin c → FieldPoly c F := fun i => gs.get ⟨i.val, by omega⟩
  have hlist : Set.range f = {p | p ∈ gs} := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact List.get_mem gs _
    · intro hp
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
      exact ⟨⟨i.val, by omega⟩, hi⟩
  have hideal : Ideal.span (Set.range f) = Ideal.ofList gs := by
    rw [hlist]
  have hgsmin := mem_minimalPrimes_of_localized_radical (Ideal.ofList gs) P hgsrad
  have hfdeg (i : Fin c) : (f i).totalDegree ≤ L := hdeg _ (List.get_mem gs _)
  have hfin := finiteLength_localized_minimal_quotient
    (Ideal.span (Set.range f)) P (hideal ▸ hgsmin)
  have hmap : (Ideal.span (Set.range f)).map
      (algebraMap (FieldPoly c F) (OriginLocalRing c F)) =
      Ideal.span (Set.range (fun i => algebraMap (FieldPoly c F) (OriginLocalRing c F) (f i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hmap] at hfin
  refine ⟨f, ?_, Module.length_ne_top_iff.mpr hfin |>.lt_top⟩
  intro i
  refine ⟨hfdeg i, ?_⟩
  rw [← hrange]
  apply hcontain
  change f i ∈ Ideal.span {p | p ∈ gs}
  exact Ideal.subset_span (List.get_mem gs _)

end
end DistinctDistances.TrackA
