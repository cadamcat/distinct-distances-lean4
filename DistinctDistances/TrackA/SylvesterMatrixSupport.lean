import DistinctDistances.TrackA.SylvesterSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open OAI.PermanentBorder.PlaneHilbert OAI.PermanentBorder.SliceParameters
open OAI.PermanentBorder.Multigraded
variable {K : Type*} [Field K]

def sylvesterExponent (d : ℕ) (i : Fin (d+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (d-i.val) + Finsupp.single 1 i.val

theorem sylvesterExponent_degree (d : ℕ) (i : Fin (d+1)) :
    (sylvesterExponent d i).degree = d := by
  rw [degree_fin_two]
  simp only [sylvesterExponent, Finsupp.add_apply, Finsupp.single_apply,
    show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    ↓reduceIte, add_zero, zero_add]
  omega

def sylvesterCoordinates (d : ℕ) : H (K := K) (d : ℤ) ≃ₗ[K] (Fin (d+1) → K) :=
  (pieceCoordinates (d : ℤ)).trans
    (LinearEquiv.piCongrLeft' K (fun _ => K) ((degreeIndexEquiv d).trans Fin.revPerm))

theorem sylvesterCoordinates_apply (d : ℕ) (p : H (K := K) (d : ℤ)) (i : Fin (d+1)) :
    sylvesterCoordinates d p i = p.val.coeff (sylvesterExponent d i) := by
  change p.val.coeff (((degreeIndexEquiv d).symm (Fin.revPerm.symm i)).val) = _
  congr 1
  ext j
  fin_cases j <;> simp [degreeIndexEquiv, Fin.revPerm, Fin.rev, sylvesterExponent] <;> omega

def sylvesterBasis (d : ℕ) : Module.Basis (Fin (d+1)) K (H (K := K) (d : ℤ)) :=
  (Pi.basisFun K (Fin (d+1))).map (sylvesterCoordinates d).symm

theorem sylvesterBasis_val (d : ℕ) (j : Fin (d+1)) :
    (sylvesterBasis (K := K) d j).val = MvPolynomial.monomial (sylvesterExponent d j) 1 := by
  let m : H (K := K) (d : ℤ) :=
    ⟨MvPolynomial.monomial (sylvesterExponent d j) 1,
      MvPolynomial.isWeightedHomogeneous_monomial _ _ _
        ((intWeight_degree _).trans (by rw [sylvesterExponent_degree]))⟩
  have hm : sylvesterCoordinates d m = Pi.basisFun K (Fin (d+1)) j := by
    ext i
    rw [sylvesterCoordinates_apply]
    have he : sylvesterExponent d j = sylvesterExponent d i ↔ j = i := by
      constructor
      · intro h
        apply Fin.ext
        simpa [sylvesterExponent] using congrArg (fun s : Fin 2 →₀ ℕ => s 1) h
      · rintro rfl
        rfl
    simp [m, MvPolynomial.coeff_monomial, Pi.basisFun_apply, Pi.single_apply, he, eq_comm]
  have hb : sylvesterCoordinates d (sylvesterBasis d j) = Pi.basisFun K (Fin (d+1)) j := by
    simp [sylvesterBasis, Module.Basis.map_apply]
  exact congrArg Subtype.val ((sylvesterCoordinates d).injective (hb.trans hm.symm))

def sylvesterInputExponent (L : ℕ) (a : Fin L) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (L-1-a.val) + Finsupp.single 1 a.val

def sylvesterOutputExponent (L : ℕ) (i : Fin (2*L)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (2*L-1-i.val) + Finsupp.single 1 i.val

def sylvesterDegreeBasis (N : ℕ) (hN : 1 ≤ N) :
    Module.Basis (Fin N) K (H (K := K) ((N : ℤ)-1)) :=
  ((sylvesterBasis (K := K) (N-1)).reindex (finCongr (by omega))).map
    (LinearEquiv.ofEq (H (K := K) ((N-1 : ℕ) : ℤ)) (H (K := K) ((N : ℤ)-1))
      (by congr 1; omega))

theorem sylvesterDegreeBasis_val (N : ℕ) (hN : 1 ≤ N) (i : Fin N) :
    (sylvesterDegreeBasis (K := K) N hN i).val =
      MvPolynomial.monomial (sylvesterInputExponent N i) 1 := by
  simp only [sylvesterDegreeBasis, Module.Basis.map_apply, Module.Basis.reindex_apply]
  change (sylvesterBasis (N-1) _).val = _
  rw [sylvesterBasis_val]
  rfl

theorem sylvesterDegreeBasis_repr (N : ℕ) (hN : 1 ≤ N)
    (p : H (K := K) ((N : ℤ)-1)) (i : Fin N) :
    (sylvesterDegreeBasis N hN).repr p i = p.val.coeff (sylvesterInputExponent N i) := by
  simp only [sylvesterDegreeBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Module.Basis.repr_reindex_apply]
  simp only [sylvesterBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Pi.basisFun_repr, LinearEquiv.symm_symm]
  rw [sylvesterCoordinates_apply]
  rfl

def sylvesterInputEquiv (L : ℕ) : Fin L ⊕ Fin L ≃ Fin (2*L) :=
  finSumFinEquiv.trans (finCongr (by omega))

def sylvesterProductBasis (L : ℕ) (hL : 1 ≤ L) :
    Module.Basis (Fin (2*L)) K (H (K := K) ((L : ℤ)-1) × H (K := K) ((L : ℤ)-1)) :=
  ((sylvesterDegreeBasis L hL).prod (sylvesterDegreeBasis L hL)).reindex
    (sylvesterInputEquiv L)

def sylvesterSectionMap (L : ℕ) (f g : Plane (K := K))
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L) :
    (H (K := K) ((L : ℤ)-1) × H (K := K) ((L : ℤ)-1)) →ₗ[K]
      H (K := K) (2*(L : ℤ)-1) :=
  let e := LinearEquiv.ofEq (H (K := K) ((L : ℤ)-1))
    (H (K := K) ((2*(L : ℤ)-1)-L)) (by congr 1; ring)
  ((mulPiece weight (homogeneous_intWeight hf) (2*(L : ℤ)-1)).comp e.toLinearMap).coprod
    ((mulPiece weight (homogeneous_intWeight hg) (2*(L : ℤ)-1)).comp e.toLinearMap)

theorem sylvesterSectionMap_val (L : ℕ) (f g : Plane (K := K))
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L)
    (a : H (K := K) ((L : ℤ)-1) × H (K := K) ((L : ℤ)-1)) :
    (sylvesterSectionMap L f g hf hg a).val = f*a.1.val + g*a.2.val := rfl

theorem sylvesterSectionMap_range (L : ℕ) (f g : Plane (K := K))
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L) :
    LinearMap.range (sylvesterSectionMap L f g hf hg) =
      multiplicationRange (homogeneous_intWeight hf) (2*(L : ℤ)-1) ⊔
        multiplicationRange (homogeneous_intWeight hg) (2*(L : ℤ)-1) := by
  unfold sylvesterSectionMap
  rw [LinearMap.range_coprod]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.ofEq _ _ _).range,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.ofEq _ _ _).range]

/-- Coefficients of the actual multiplication columns, with both the
natural-subtraction guards from the frozen Sylvester matrix. -/
theorem sylvester_coeff_column (L : ℕ) (hL : 1 ≤ L) (f : Plane (K := K))
    (i : Fin (2*L)) (a : Fin L) :
    (f * MvPolynomial.monomial (sylvesterInputExponent L a) 1).coeff
      (sylvesterOutputExponent L i) =
      if a.val ≤ i.val ∧ i.val-a.val ≤ L then
        binaryCoeff f (L-(i.val-a.val)) (i.val-a.val) else 0 := by
  have hle : sylvesterInputExponent L a ≤ sylvesterOutputExponent L i ↔
      a.val ≤ i.val ∧ i.val-a.val ≤ L := by
    constructor
    · intro h
      have h0 := h 0
      have h1 := h 1
      simp only [sylvesterInputExponent, sylvesterOutputExponent, Finsupp.add_apply,
        Finsupp.single_apply, show (0 : Fin 2) ≠ 1 by decide,
        show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, add_zero, zero_add] at h0 h1
      omega
    · intro h
      intro j
      fin_cases j <;> simp [sylvesterInputExponent, sylvesterOutputExponent,
        Finsupp.single_apply] <;> omega
  rw [MvPolynomial.coeff_mul_monomial']
  simp only [hle, mul_one]
  split_ifs with h
  · have he : sylvesterOutputExponent L i - sylvesterInputExponent L a =
        Finsupp.single 0 (L-(i.val-a.val)) + Finsupp.single 1 (i.val-a.val) := by
      ext j
      fin_cases j <;> simp [sylvesterInputExponent, sylvesterOutputExponent,
        Finsupp.single_apply] <;> omega
    rw [he]
    rfl
  · rfl

/-- The frozen coefficient formula is the matrix of the homogeneous
section map in the monomial bases, including the two endpoint monomials. -/
theorem sylvesterSectionMap_matrix (L : ℕ) (hL : 1 ≤ L) (f g : Plane (K := K))
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L) :
    (sylvesterSectionMap L f g hf hg).toMatrix
      (sylvesterProductBasis L hL) (sylvesterDegreeBasis (2*L) (by omega)) =
      sylvesterMatrix L f g := by
  ext i j
  rw [LinearMap.toMatrix_apply, sylvesterDegreeBasis_repr]
  obtain ⟨a, rfl⟩ := (sylvesterInputEquiv L).surjective j
  cases a with
  | inl a =>
    simp only [sylvesterProductBasis, Module.Basis.reindex_apply,
      Equiv.symm_apply_apply]
    rw [sylvesterSectionMap_val, Module.Basis.prod_apply_inl_fst,
      Module.Basis.prod_apply_inl_snd, sylvesterDegreeBasis_val]
    simp only [ZeroMemClass.coe_zero, mul_zero, add_zero]
    change (f * MvPolynomial.monomial (sylvesterInputExponent L a) 1).coeff
      (sylvesterOutputExponent L i) = _
    rw [sylvester_coeff_column L hL]
    have hj : (sylvesterInputEquiv L (Sum.inl a)).val = a.val := rfl
    simp only [sylvesterMatrix, hj, if_pos a.isLt]
  | inr a =>
    simp only [sylvesterProductBasis, Module.Basis.reindex_apply,
      Equiv.symm_apply_apply]
    rw [sylvesterSectionMap_val, Module.Basis.prod_apply_inr_fst,
      Module.Basis.prod_apply_inr_snd, sylvesterDegreeBasis_val]
    simp only [ZeroMemClass.coe_zero, mul_zero, zero_add]
    change (g * MvPolynomial.monomial (sylvesterInputExponent L a) 1).coeff
      (sylvesterOutputExponent L i) = _
    rw [sylvester_coeff_column L hL]
    have hj : (sylvesterInputEquiv L (Sum.inr a)).val = L+a.val := rfl
    have hnlt : ¬ L+a.val < L := by omega
    simp only [sylvesterMatrix, hj, if_neg hnlt, Nat.add_sub_cancel_left]

theorem sylvester_rank_eq_range (L : ℕ) (hL : 1 ≤ L) (f g : Plane (K := K))
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L) :
    Matrix.rank (sylvesterMatrix L f g) =
      Module.finrank K (LinearMap.range (sylvesterSectionMap L f g hf hg)) := by
  rw [← sylvesterSectionMap_matrix L hL f g hf hg]
  rw [Matrix.rank_eq_finrank_range_toLin _
    (sylvesterDegreeBasis (2*L) (by omega)) (sylvesterProductBasis L hL)]
  rw [Matrix.toLin_toMatrix]
  rfl

theorem sylvester_rank_core (L : ℕ) (hL : 1 ≤ L) (f g : Plane (K := K))
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L) (hnonzero : f ≠ 0 ∨ g ≠ 0) :
    Matrix.rank (sylvesterMatrix L f g) = 2*L-(binaryGcd f g).totalDegree := by
  rw [sylvester_rank_eq_range L hL f g hf hg, sylvesterSectionMap_range]
  have hdim : (2*(L : ℤ)-1-(L : ℤ)+1).toNat = L := by omega
  by_cases hf0 : f = 0
  · have hg0 : g ≠ 0 := by simpa only [hf0, ne_eq, not_true_eq_false, false_or] using hnonzero
    have hdeg : (binaryGcd f g).totalDegree = L := by
      rw [hf0, sylvester_gcd_degree_zero_left g hg0, hg.totalDegree hg0]
    rw [sylvester_range_zero (homogeneous_intWeight hf) hf0, bot_sup_eq,
      finrank_multiplicationRange (homogeneous_intWeight hg) hg0, hdim, hdeg]
    omega
  · by_cases hg0 : g = 0
    · have hdeg : (binaryGcd f g).totalDegree = L := by
        rw [hg0, sylvester_gcd_degree_zero_right f hf0, hf.totalDegree hf0]
      rw [sylvester_range_zero (homogeneous_intWeight hg) hg0, sup_bot_eq,
        finrank_multiplicationRange (homogeneous_intWeight hf) hf0, hdim, hdeg]
      omega
    · obtain ⟨hd, hh, u, v, hu, hv, hh0, hu0, hv0, huv, huw, hvw⟩ :=
        sylvester_gcd_factors f g L hf hg hf0 hg0
      have hrf := sylvester_range_congr (homogeneous_intWeight hf) (hh.mul huw)
        hu (by ring) (2*(L : ℤ)-1)
      have hrg := sylvester_range_congr (homogeneous_intWeight hg) (hh.mul hvw)
        hv (by ring) (2*(L : ℤ)-1)
      rw [hrf, hrg]
      exact sylvester_range_rank L (binaryGcd f g).totalDegree hd hh huw hvw
        hh0 hu0 hv0 huv

end
end DistinctDistances.TrackA
