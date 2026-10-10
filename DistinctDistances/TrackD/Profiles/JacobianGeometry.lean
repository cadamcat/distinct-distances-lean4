import DistinctDistances.TrackD.Profiles.Budget
import DistinctDistances.TrackD.GenericTangent
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Algebraic rank and tangent steps of `prof:regularity.jacobian`,
`profiles.tex:385–401`. All exceptional-mass estimates are separate hypotheses. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

set_option maxHeartbeats 1000000

def evaluatedJacobian (E : List (Poly d)) (x : Point d) :
    Matrix (Fin E.length) (Fin d) ℂ :=
  (TrackA.jacobian E).map (MvPolynomial.eval x)

theorem evaluatedJacobian_kernel (E : List (Poly d)) (x : Point d) :
    LinearMap.ker (evaluatedJacobian E x).mulVecLin = jacKer E.toFinset x := by
  ext v
  simp only [LinearMap.mem_ker, jacKer, Submodule.mem_iInf]
  constructor
  · intro hv f hf
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hf)
    have h := congrFun hv i
    have h' : differential (E.get i) x v = 0 := by
      simpa [evaluatedJacobian, TrackA.jacobian, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, differential, LinearMap.sum_apply,
        LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul] using h
    simpa only [hi] using h' 
  · intro hv
    funext i
    have h := hv (E.get i) (List.mem_toFinset.mpr (List.get_mem E i))
    simpa [evaluatedJacobian, TrackA.jacobian, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, differential, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul] using h

/-- Nonvanishing of a linear combination of q-minors forces codimension at least q.
The certificate is evaluated at the actual point, including points outside the family. -/
theorem minor_certificate_finrank (E : List (Poly d)) (q : ℕ) (g : Poly d)
    (hg : g ∈ Submodule.span ℂ (TrackA.jacobianMinors E q))
    (x : Point d) (hx : MvPolynomial.eval x g ≠ 0) :
    Module.finrank ℂ (jacKer E.toFinset x) + q ≤ d := by
  have hex : ∃ f ∈ TrackA.jacobianMinors E q, MvPolynomial.eval x f ≠ 0 := by
    by_contra hn
    push Not at hn
    have hzero : ∀ p ∈ Submodule.span ℂ (TrackA.jacobianMinors E q),
        MvPolynomial.eval x p = 0 := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem f hf => exact hn f hf
      | zero => simp
      | add f h hf hh ihf ihh => simp [map_add, ihf, ihh]
      | smul a f hf ih => simpa using congrArg (fun z : ℂ => a * z) ih
    exact hx (hzero g hg)
  obtain ⟨f, ⟨rows, cols, rfl⟩, hf⟩ := hex
  have hdet : ((evaluatedJacobian E x).submatrix rows cols).det ≠ 0 := by
    have heq : ((evaluatedJacobian E x).submatrix rows cols).det =
        MvPolynomial.eval x ((TrackA.jacobian E).submatrix rows cols).det := by
      rw [RingHom.map_det]
      rfl
    rw [heq]
    exact hf
  have hrank : q ≤ (evaluatedJacobian E x).rank := by
    have h := Matrix.rank_submatrix_le (evaluatedJacobian E x) rows cols
    rwa [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
  have hdim := LinearMap.finrank_range_add_finrank_ker (evaluatedJacobian E x).mulVecLin
  rw [evaluatedJacobian_kernel] at hdim
  have hdim' : (evaluatedJacobian E x).rank + Module.finrank ℂ (jacKer E.toFinset x) = d := by
    simpa [Matrix.rank] using hdim
  omega

/-- Matrix rank at a fixed point persists on a principal open. A square matrix is enough
because a basis of the tangent equations has at most d rows. -/
theorem polynomial_matrix_rank_open (M : Matrix (Fin d) (Fin d) (Poly d)) (x : Point d) :
    ∃ g : Poly d, MvPolynomial.eval x g ≠ 0 ∧
      ∀ y : Point d, MvPolynomial.eval y g ≠ 0 →
        (M.map (MvPolynomial.eval x)).rank ≤ (M.map (MvPolynomial.eval y)).rank := by
  obtain ⟨V, U, e, _, _, hnormal⟩ := Matrix.exists_rank_normal_form (M.map (MvPolynomial.eval x))
  let r := (M.map (MvPolynomial.eval x)).rank
  let rows : Fin r → Fin d := fun i => e.symm (Sum.inl i)
  let N := V.map MvPolynomial.C * M * U.map MvPolynomial.C
  let P := N.submatrix rows rows
  have hmap (y : Point d) : N.map (MvPolynomial.eval y) = V * M.map (MvPolynomial.eval y) * U := by
    have hV : (V.map MvPolynomial.C).map (MvPolynomial.eval y) = V := by
      ext i j
      simp
    have hU : (U.map MvPolynomial.C).map (MvPolynomial.eval y) = U := by
      ext i j
      simp
    simp only [N, Matrix.map_mul, hV, hU]
  have hP : P.map (MvPolynomial.eval x) = 1 := by
    change (N.map (MvPolynomial.eval x)).submatrix rows rows = 1
    rw [hmap, hnormal]
    ext i j
    simp [rows, Matrix.submatrix, Matrix.fromBlocks, Matrix.one_apply]
  have hdet : MvPolynomial.eval x P.det = 1 := by
    rw [RingHom.map_det]
    change (P.map (MvPolynomial.eval x)).det = 1
    rw [hP, Matrix.det_one]
  refine ⟨P.det, by rw [hdet]; exact one_ne_zero, ?_⟩
  intro y hy
  have hyP : (P.map (MvPolynomial.eval y)).det ≠ 0 := by
    change ((MvPolynomial.eval y).mapMatrix P).det ≠ 0
    rwa [← RingHom.map_det]
  calc
    (M.map (MvPolynomial.eval x)).rank = (P.map (MvPolynomial.eval y)).rank := by
      rw [Matrix.rank_of_det_ne_zero hyP, Fintype.card_fin]
    _ ≤ (N.map (MvPolynomial.eval y)).rank :=
      Matrix.rank_submatrix_le (N.map (MvPolynomial.eval y)) rows rows
    _ ≤ (M.map (MvPolynomial.eval y)).rank := by
      rw [hmap]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Choose d (possibly zero) ideal equations giving the entire tangent kernel at x.
Only a basis of the span of differentials is needed; no degree bound is claimed. -/
theorem tangent_square_equations (X : AffineVariety d) (x : Point d) :
    ∃ f : Fin d → Poly d, (∀ i, f i ∈ X.ideal) ∧
      LinearMap.ker (Matrix.map (fun i j => MvPolynomial.pderiv j (f i) :
        Matrix (Fin d) (Fin d) (Poly d)) (MvPolynomial.eval x)).mulVecLin =
        X.tangentSpace x := by
  let S : Set (Module.Dual ℂ (Point d)) := {l | ∃ p ∈ X.ideal, differential p x = l}
  let r := Module.finrank ℂ (Submodule.span ℂ S)
  obtain ⟨v, hv, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ S
  have hr : r ≤ d := by
    have h := Submodule.finrank_le (Submodule.span ℂ S)
    simpa [r, Subspace.dual_finrank_eq] using h
  have hchoose (i : Fin r) : ∃ p ∈ X.ideal, differential p x = v i := hv i
  choose p hp hdiff using hchoose
  let f : Fin d → Poly d := fun i => if hi : i.val < r then p ⟨i.val, hi⟩ else 0
  have hf : ∀ i, f i ∈ X.ideal := by
    intro i
    dsimp [f]
    split_ifs with hi
    · exact hp ⟨i.val, hi⟩
    · exact X.ideal.zero_mem
  refine ⟨f, hf, ?_⟩
  ext u
  simp only [LinearMap.mem_ker, AffineVariety.tangentSpace, Submodule.mem_iInf]
  constructor
  · intro hu q
    have huv : ∀ i : Fin r, v i u = 0 := by
      intro i
      have h := congrFun hu (⟨i.val, i.isLt.trans_le hr⟩ : Fin d)
      change (∑ k, MvPolynomial.eval x (MvPolynomial.pderiv k
        (f ⟨i.val, i.isLt.trans_le hr⟩)) * u k) = 0 at h
      have hfval : f ⟨i.val, i.isLt.trans_le hr⟩ = p i := by simp [f, i.isLt]
      simpa [Matrix.mulVecLin_apply, Matrix.map_apply, Matrix.mulVec, dotProduct,
        hfval, ← hdiff i, differential, LinearMap.sum_apply,
        LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul] using h
    have hq : differential q.val x ∈ Submodule.span ℂ (Set.range v) := by
      rw [hspan]
      exact Submodule.subset_span ⟨q.val, q.property, rfl⟩
    have hzero : ∀ l ∈ Submodule.span ℂ (Set.range v), l u = 0 := by
      intro l hl
      induction hl using Submodule.span_induction with
      | mem l hl => obtain ⟨i, rfl⟩ := hl; exact huv i
      | zero => simp
      | add a b ha hb iha ihb => simp [iha, ihb]
      | smul c a ha ih => simp [ih]
    exact hzero _ hq
  · intro hu
    funext i
    have h := hu ⟨f i, hf i⟩
    change (∑ k, MvPolynomial.eval x (MvPolynomial.pderiv k (f i)) * u k) = 0
    simpa [differential, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul] using h

/-- Tangent dimension cannot drop below the dimension of an irreducible carrier.
Rank persistence transfers a hypothetical drop to the known generic tangent dimension. -/
theorem tangent_finrank_ge_dimension (X : AffineVariety d) (hX : X.IsIrreducible)
    (x : Point d) (hx : x ∈ X) : X.dimension ≤ Module.finrank ℂ (X.tangentSpace x) := by
  obtain ⟨f, hf, hker⟩ := tangent_square_equations X x
  let M : Matrix (Fin d) (Fin d) (Poly d) := fun i j => MvPolynomial.pderiv j (f i)
  obtain ⟨g, hgx, hgrank⟩ := polynomial_matrix_rank_open M x
  have hopen : ForGeneralPoint X (fun y => MvPolynomial.eval y g ≠ 0) :=
    ⟨g, ⟨x, hx, hgx⟩, fun y hy hgy => hgy⟩
  obtain ⟨y, hy, hdim, hgy⟩ := ((general_tangent_finrank X hX).and hX hopen).exists
  have hle : X.tangentSpace y ≤ LinearMap.ker (M.map (MvPolynomial.eval y)).mulVecLin := by
    intro u hu
    rw [LinearMap.mem_ker]
    funext i
    have h := (Submodule.mem_iInf _).mp hu ⟨f i, hf i⟩
    change (∑ k, MvPolynomial.eval y (MvPolynomial.pderiv k (f i)) * u k) = 0
    simpa [differential, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul] using h
  have hmono := Submodule.finrank_mono hle
  rw [hdim] at hmono
  have hrank := hgrank y hgy
  have hxsum := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (M.map (MvPolynomial.eval x)).mulVecLin
  have hysum := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (M.map (MvPolynomial.eval y)).mulVecLin
  change LinearMap.ker (M.map (MvPolynomial.eval x)).mulVecLin = X.tangentSpace x at hker
  rw [hker] at hxsum
  change (M.map (MvPolynomial.eval x)).rank +
    Module.finrank ℂ (X.tangentSpace x) = Module.finrank ℂ (Point d) at hxsum
  change (M.map (MvPolynomial.eval y)).rank +
    Module.finrank ℂ (LinearMap.ker (M.map (MvPolynomial.eval y)).mulVecLin) =
      Module.finrank ℂ (Point d) at hysum
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hxsum hysum
  have hbound : Module.finrank ℂ (LinearMap.ker (M.map (MvPolynomial.eval y)).mulVecLin) ≤
      Module.finrank ℂ (X.tangentSpace x) := by omega
  exact hmono.trans hbound

theorem tangent_le_jacKer (Z : AffineVariety d) (E : Finset (Poly d))
    (hE : ∀ f ∈ E, f ∈ Z.ideal) (x : Point d) : Z.tangentSpace x ≤ jacKer E x := by
  intro v hv
  simp only [jacKer, Submodule.mem_iInf]
  intro f hf
  exact (Submodule.mem_iInf _).mp hv ⟨f, hE f hf⟩

/-- With pure carriers, a maximal-minor certificate gives the exact carrier tangent
and smoothness. This proof does not transfer smoothness through an analytic germ. -/
theorem carrier_smooth_of_minor (Z : AffineVariety d) (hZ : Z.IsIrreducible)
    (j : ℕ) (hj : j ≤ d) (hdim : Z.dimension = d - j)
    (E : List (Poly d)) (hE : ∀ f ∈ E, f ∈ Z.ideal)
    (g : Poly d) (hg : g ∈ Submodule.span ℂ (TrackA.jacobianMinors E j))
    (x : Point d) (hx : x ∈ Z) (hgx : MvPolynomial.eval x g ≠ 0) :
    Z.IsSmoothAt x ∧ Z.tangentSpace x = jacKer E.toFinset x := by
  have hle := tangent_le_jacKer Z E.toFinset (fun f hf => hE f (List.mem_toFinset.mp hf)) x
  have hlo := tangent_finrank_ge_dimension Z hZ x hx
  have hhi := minor_certificate_finrank E j g hg x hgx
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [hdim] at hlo; omega)
  have htandim : Module.finrank ℂ (Z.tangentSpace x) = Z.dimension := by
    have hm := Submodule.finrank_mono hle
    rw [hdim] at hlo ⊢
    omega
  refine ⟨⟨hx, ?_⟩, heq⟩
  rw [Z.localDimension_eq_dimension x hZ hx]
  exact htandim

theorem local_carrier_exists (X : Piece d) (x : Pt d) (hx : x ∈ X.pts)
    (hvan : ∀ i, MvPolynomial.eval (toC x) (X.path.cut i) = 0) (j : ℕ) :
    ∃ Z, Z ∈ X.path.localCarriers j (toC x) := by
  have hsys : X.path.system j ≤ pointIdeal (toC x) := by
    apply Ideal.span_le.mpr
    rintro f ⟨i, hi, rfl⟩
    change X.path.cut i ∈ MvPolynomial.vanishingIdeal ℂ {toC x}
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    have hyx : y = toC x := Set.mem_singleton_iff.mp hy
    subst y
    exact hvan i
  obtain ⟨I, hI, hIx⟩ := Ideal.exists_minimalPrimes_le hsys
  let Z : AffineVariety d := ⟨I, hI.isPrime.isRadical⟩
  refine ⟨Z, hI, ?_⟩
  intro f hf
  exact MvPolynomial.mem_vanishingIdeal_iff.mp (hIx hf) (toC x) (by simp)

/-- Finite-family version of JacRegularAt; the pool is only used when transferring
family membership back to PoolCarrier. -/
def FamilyJacRegularAt (F : AffineFamily.Family d) (E : List (Poly d)) (g : Poly d)
    (y : Point d) : Prop :=
  MvPolynomial.eval y g ≠ 0 ∧
    ∃ Z, (Z ∈ F ∧ y ∈ Z) ∧
      (∀ Z', Z' ∈ F ∧ y ∈ Z' → Z' = Z) ∧
      Z.IsSmoothAt y ∧ Z.tangentSpace y = jacKer E.toFinset y

/-- Per-piece accounting for a common certificate. The exceptional mass and the
proper-cut mass are supplied separately, so no factor equal to the pool size appears. -/
theorem jacobian_bad_points_accounting (X : Piece d) (j : ℕ) (hj : j ≤ d)
    (hvan : ∀ x ∈ X.pts, ∀ i, MvPolynomial.eval (toC x) (X.path.cut i) = 0)
    (F bad : AffineFamily.Family d) (E : List (Poly d)) (g : Poly d)
    (hF : ∀ x ∈ X.pts, ∀ Z ∈ X.path.localCarriers j (toC x), Z ∈ F)
    (hpure : AffineFamily.IsPure F (d - j))
    (hE : ∀ Z ∈ F, ∀ f ∈ E, f ∈ Z.ideal)
    (hg : g ∈ Submodule.span ℂ (TrackA.jacobianMinors E j))
    (hproper : ∀ Z ∈ F, Z ∉ bad → g ∉ Z.ideal)
    (hunique : ∀ y : Point d, MvPolynomial.eval y g ≠ 0 →
      ∀ Z ∈ F, ∀ Z' ∈ F, y ∈ Z → y ∈ Z' → Z = Z')
    (δ ε : ℝ)
    (hbad : ((X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x),
      Z ∈ bad)).card : ℝ) ≤ δ * X.pts.card)
    (hcuts : ((X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x),
      g ∉ Z.ideal ∧ MvPolynomial.eval (toC x) g = 0)).card : ℝ) ≤ ε * X.pts.card) :
    ((X.pts.filter (fun x => ¬ FamilyJacRegularAt F E g (toC x))).card : ℝ) ≤
      (δ + ε) * X.pts.card := by
  let B := X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad)
  let C := X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x),
    g ∉ Z.ideal ∧ MvPolynomial.eval (toC x) g = 0)
  have hsub : X.pts.filter (fun x => ¬ FamilyJacRegularAt F E g (toC x)) ⊆ B ∪ C := by
    intro x hx
    obtain ⟨hxX, hnot⟩ := Finset.mem_filter.mp hx
    obtain ⟨Z, hZ⟩ := local_carrier_exists X x hxX (hvan x hxX) j
    have hZF := hF x hxX Z hZ
    by_cases hzero : MvPolynomial.eval (toC x) g = 0
    · by_cases hZbad : Z ∈ bad
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxX, Z, hZ, hZbad⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hxX, Z, hZ, hproper Z hZF hZbad, hzero⟩)
    · apply False.elim
      apply hnot
      refine ⟨hzero, Z, ⟨hZF, hZ.2⟩, ?_, ?_⟩
      · intro Z' hZ'
        exact hunique (toC x) hzero Z' hZ'.1 Z hZF hZ'.2 hZ.2
      · exact carrier_smooth_of_minor Z (hpure Z hZF).1 j hj (hpure Z hZF).2
          E (hE Z hZF) g hg (toC x) hZ.2 hzero
  have hcard : (X.pts.filter (fun x => ¬ FamilyJacRegularAt F E g (toC x))).card ≤
      B.card + C.card := (Finset.card_le_card hsub).trans (Finset.card_union_le B C)
  have hcardR : ((X.pts.filter (fun x => ¬ FamilyJacRegularAt F E g (toC x))).card : ℝ) ≤
      (B.card : ℝ) + C.card := by exact_mod_cast hcard
  calc
    _ ≤ (B.card : ℝ) + C.card := hcardR
    _ ≤ δ * X.pts.card + ε * X.pts.card := add_le_add hbad hcuts
    _ = (δ + ε) * X.pts.card := by ring

end
end DistinctDistances.TrackD
