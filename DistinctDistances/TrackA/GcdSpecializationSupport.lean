import DistinctDistances.TrackA.RankSpecializationSupport
import DistinctDistances.TrackA.DepthDefinitions
import DistinctDistances.TrackA.BinaryDivisorSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

theorem sylvesterMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (L : ℕ) (F G : MvPolynomial (Fin 2) R) :
    (sylvesterMatrix L F G).map φ =
      sylvesterMatrix L (MvPolynomial.map φ F) (MvPolynomial.map φ G) := by
  ext i j
  simp only [sylvesterMatrix, Matrix.map_apply, binaryCoeff, MvPolynomial.coeff_map]
  split_ifs <;> simp

theorem binary_gcd_degree_le {K : Type*} [Field K]
    (f g : MvPolynomial (Fin 2) K) (L : ℕ)
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L) :
    (binaryGcd f g).totalDegree ≤ L := by
  letI : NormalizedGCDMonoid (MvPolynomial (Fin 2) K) := Classical.arbitrary _
  change (gcd f g).totalDegree ≤ L
  by_cases hf0 : f = 0
  · by_cases hg0 : g = 0
    · simp [hf0, hg0]
    · exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain
        (gcd_dvd_right f g) hg0).trans (hg.totalDegree_le)
  · exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain
      (gcd_dvd_left f g) hf0).trans (hf.totalDegree_le)

theorem generic_binary_zero_specializes {d : ℕ} (X : AffineVariety d)
    (hX : X.IsIrreducible) (F : BinaryForm d) (p : Point d) (hp : p ∈ X.points) :
    letI : X.ideal.IsPrime := hX
    let K := FractionRing (Poly d ⧸ X.ideal)
    let η : Poly d →+* K :=
      (algebraMap (Poly d ⧸ X.ideal) K).comp (Ideal.Quotient.mk X.ideal)
    MvPolynomial.map η F = 0 → specializeBinary F p = 0 := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  change MvPolynomial.map
    ((algebraMap R K).comp (Ideal.Quotient.mk X.ideal)) F = 0 → specializeBinary F p = 0
  intro hz
  ext m
  have hm := congrArg (fun H : MvPolynomial (Fin 2) K => H.coeff m) hz
  change algebraMap R K (Ideal.Quotient.mk X.ideal (F.coeff m)) = 0 at hm
  have hq : Ideal.Quotient.mk X.ideal (F.coeff m) = 0 :=
    IsFractionRing.injective R K (hm.trans (map_zero (algebraMap R K)).symm)
  have hi := Ideal.Quotient.eq_zero_iff_mem.mp hq
  have hp0 := hp (F.coeff m) hi
  simpa [specializeBinary, MvPolynomial.coeff_map, MvPolynomial.aeval_eq_eval] using hp0

/-- Rank specialization applies to the actual quotient carrier; evaluation
at its point factors through that quotient even at singular points. -/
theorem sylvester_rank_specialization {d : ℕ} (X : AffineVariety d)
    (hX : X.IsIrreducible) (F G : BinaryForm d) (L : ℕ)
    (p : Point d) (hp : p ∈ X.points) :
    letI : X.ideal.IsPrime := hX
    let K := FractionRing (Poly d ⧸ X.ideal)
    let η : Poly d →+* K :=
      (algebraMap (Poly d ⧸ X.ideal) K).comp (Ideal.Quotient.mk X.ideal)
    (sylvesterMatrix L (specializeBinary F p) (specializeBinary G p)).rank ≤
      (sylvesterMatrix L (MvPolynomial.map η F) (MvPolynomial.map η G)).rank := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  let φ : R →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ X.ideal (MvPolynomial.aeval p)
    (fun f hf => hp f hf)
  let ψ : R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ R K
  let η : Poly d →+* K := (algebraMap R K).comp (Ideal.Quotient.mk X.ideal)
  let Fq := MvPolynomial.map (Ideal.Quotient.mk X.ideal) F
  let Gq := MvPolynomial.map (Ideal.Quotient.mk X.ideal) G
  have hφ (f : Poly d) : φ (Ideal.Quotient.mk X.ideal f) = MvPolynomial.eval p f := by
    change Ideal.Quotient.lift X.ideal (MvPolynomial.aeval p).toRingHom
      (fun f hf => hp f hf) (Ideal.Quotient.mk X.ideal f) = MvPolynomial.eval p f
    rw [Ideal.Quotient.lift_mk]
    exact congrFun (MvPolynomial.aeval_eq_eval p) f
  have hFφ : MvPolynomial.map φ.toRingHom Fq = specializeBinary F p := by
    ext m
    simp only [MvPolynomial.coeff_map, Fq, specializeBinary]
    exact hφ _
  have hGφ : MvPolynomial.map φ.toRingHom Gq = specializeBinary G p := by
    ext m
    simp only [MvPolynomial.coeff_map, Gq, specializeBinary]
    exact hφ _
  have hFψ : MvPolynomial.map ψ.toRingHom Fq = MvPolynomial.map η F := by
    ext m
    rfl
  have hGψ : MvPolynomial.map ψ.toRingHom Gq = MvPolynomial.map η G := by
    ext m
    rfl
  have hr := rank_at_point_le_generic φ ψ (IsFractionRing.injective R K)
    (sylvesterMatrix L Fq Gq)
  change ((sylvesterMatrix L Fq Gq).map φ.toRingHom).rank ≤
    ((sylvesterMatrix L Fq Gq).map ψ.toRingHom).rank at hr
  rw [sylvesterMatrix_map, sylvesterMatrix_map, hFφ, hGφ, hFψ, hGψ] at hr
  exact hr

end
end DistinctDistances.TrackA
