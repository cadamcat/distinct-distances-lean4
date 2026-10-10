import DistinctDistances.TrackE.OuterPool
import OAI.NumberTheory.PowerFree.Jacobians
import Mathlib.Algebra.Module.Submodule.Union
import DistinctDistances.TrackA.SeparatorAlgebraSupport

namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

set_option maxHeartbeats 1000000

/-- The source differential tested on the connecting direction. -/
def secantSourceTest (f : Poly d) : TrackD.PairPoly d :=
  ∑ a : Fin d, MvPolynomial.rename Sum.inl (MvPolynomial.pderiv a f) *
    (MvPolynomial.X (Sum.inr a) - MvPolynomial.X (Sum.inl a))

/-- The target differential tested on the connecting direction. -/
def secantTargetTest (f : Poly d) : TrackD.PairPoly d :=
  ∑ a : Fin d, MvPolynomial.rename Sum.inr (MvPolynomial.pderiv a f) *
    (MvPolynomial.X (Sum.inr a) - MvPolynomial.X (Sum.inl a))

theorem secantSourceTest_eval (f : Poly d) (p q : Point d) :
    MvPolynomial.eval (TrackD.pairPt p q) (secantSourceTest f) =
      differential f p (q - p) := by
  simp [secantSourceTest, MvPolynomial.eval_rename, TrackD.pairPt,
    differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, Pi.sub_apply, Function.comp_def]

theorem secantTargetTest_eval (f : Poly d) (p q : Point d) :
    MvPolynomial.eval (TrackD.pairPt p q) (secantTargetTest f) =
      differential f q (q - p) := by
  simp [secantTargetTest, MvPolynomial.eval_rename, TrackD.pairPt,
    differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, Pi.sub_apply, Function.comp_def]

theorem secantSourceTest_nonzero_iff (E : Finset (Poly d)) (p q : Point d) :
    (∃ f ∈ E, MvPolynomial.eval (TrackD.pairPt p q) (secantSourceTest f) ≠ 0) ↔
      q - p ∉ TrackD.jacKer E p := by
  simp only [TrackD.jacKer, Submodule.mem_iInf, LinearMap.mem_ker,
    secantSourceTest_eval]
  push_neg
  rfl

theorem secantTargetTest_nonzero_iff (E : Finset (Poly d)) (p q : Point d) :
    (∃ f ∈ E, MvPolynomial.eval (TrackD.pairPt p q) (secantTargetTest f) ≠ 0) ↔
      q - p ∉ TrackD.jacKer E q := by
  simp only [TrackD.jacKer, Submodule.mem_iInf, LinearMap.mem_ker,
    secantTargetTest_eval]
  push_neg
  rfl

theorem secantSourceTest_degree (f : Poly d) :
    (secantSourceTest f).totalDegree ≤ f.totalDegree := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  by_cases hzero : MvPolynomial.pderiv a f = 0
  · simp [hzero]
  · have hp := OAI.QuarticPowerFree.pderiv_totalDegree_lt a f hzero
    have hr := MvPolynomial.totalDegree_rename_le
      (Sum.inl : Fin d → Fin d ⊕ Fin d) (MvPolynomial.pderiv a f)
    have hv : (MvPolynomial.X (Sum.inr a) -
        MvPolynomial.X (Sum.inl a) : TrackD.PairPoly d).totalDegree ≤ 1 := by
      simpa using MvPolynomial.totalDegree_sub
        (MvPolynomial.X (Sum.inr a) : TrackD.PairPoly d)
        (MvPolynomial.X (Sum.inl a))
    exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

theorem secantTargetTest_degree (f : Poly d) :
    (secantTargetTest f).totalDegree ≤ f.totalDegree := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  by_cases hzero : MvPolynomial.pderiv a f = 0
  · simp [hzero]
  · have hp := OAI.QuarticPowerFree.pderiv_totalDegree_lt a f hzero
    have hr := MvPolynomial.totalDegree_rename_le
      (Sum.inr : Fin d → Fin d ⊕ Fin d) (MvPolynomial.pderiv a f)
    have hv : (MvPolynomial.X (Sum.inr a) -
        MvPolynomial.X (Sum.inl a) : TrackD.PairPoly d).totalDegree ≤ 1 := by
      simpa using MvPolynomial.totalDegree_sub
        (MvPolynomial.X (Sum.inr a) : TrackD.PairPoly d)
        (MvPolynomial.X (Sum.inl a))
    exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

/-- A finite set of nonzero evaluations can be preserved in one linear combination. -/
theorem exists_polynomial_combination {n : Type*} {ι : Type*} [Fintype ι]
    (E : Finset (MvPolynomial n ℂ)) (z : ι → n → ℂ)
    (h : ∀ i, ∃ f ∈ E, MvPolynomial.eval (z i) f ≠ 0) :
    ∃ g ∈ Submodule.span ℂ (E : Set (MvPolynomial n ℂ)),
      ∀ i, MvPolynomial.eval (z i) g ≠ 0 := by
  let V := Submodule.span ℂ (E : Set (MvPolynomial n ℂ))
  let bad : ι → Submodule ℂ V := fun i =>
    LinearMap.ker ((MvPolynomial.aeval (z i)).toLinearMap.comp V.subtype)
  have hbad (i : ι) : bad i ≠ ⊤ := by
    obtain ⟨f, hf, hfi⟩ := h i
    intro ht
    let vf : V := ⟨f, Submodule.subset_span hf⟩
    have hv : vf ∈ bad i := by rw [ht]; trivial
    exact hfi (by simpa [bad, vf] using hv)
  obtain ⟨g, hg⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨g, g.property, fun i => by simpa [bad] using hg i⟩

theorem polynomial_combination_degree {n : Type*}
    (E : Finset (MvPolynomial n ℂ)) (D : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D)
    {g : MvPolynomial n ℂ} (hg : g ∈ Submodule.span ℂ (E : Set _)) :
    g.totalDegree ≤ D := by
  induction hg using Submodule.span_induction with
  | mem f hf => exact hE f hf
  | zero => simp
  | add f g hf hg ihf ihg =>
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le ihf ihg)
  | smul a f hf ih => exact (MvPolynomial.totalDegree_smul_le _ _).trans ih

theorem polynomial_combination_nonzero {n : Type*}
    (E : Finset (MvPolynomial n ℂ)) (z : n → ℂ)
    {g : MvPolynomial n ℂ} (hg : g ∈ Submodule.span ℂ (E : Set _))
    (hgn : MvPolynomial.eval z g ≠ 0) :
    ∃ f ∈ E, MvPolynomial.eval z f ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hspan : Submodule.span ℂ (E : Set _) ≤
      LinearMap.ker (MvPolynomial.aeval z).toLinearMap := by
    apply Submodule.span_le.mpr
    intro f hf
    exact hn f hf
  exact hgn (hspan hg)

theorem secantSource_combination_transverse (E : Finset (Poly d)) (p q : Point d)
    {g : TrackD.PairPoly d}
    (hg : g ∈ Submodule.span ℂ (E.image secantSourceTest : Set _))
    (hgn : MvPolynomial.eval (TrackD.pairPt p q) g ≠ 0) :
    q - p ∉ TrackD.jacKer E p := by
  obtain ⟨f, hf, hfn⟩ := polynomial_combination_nonzero _ _ hg hgn
  obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.mp hf
  exact (secantSourceTest_nonzero_iff E p q).mp ⟨f₀, hf₀, hfn⟩

theorem secantTarget_combination_transverse (E : Finset (Poly d)) (p q : Point d)
    {g : TrackD.PairPoly d}
    (hg : g ∈ Submodule.span ℂ (E.image secantTargetTest : Set _))
    (hgn : MvPolynomial.eval (TrackD.pairPt p q) g ≠ 0) :
    q - p ∉ TrackD.jacKer E q := by
  obtain ⟨f, hf, hfn⟩ := polynomial_combination_nonzero _ _ hg hgn
  obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.mp hf
  exact (secantTargetTest_nonzero_iff E p q).mp ⟨f₀, hf₀, hfn⟩

theorem physical_tangent_eq_of_rank (X : AffineVariety d) (hX : X.IsIrreducible)
    (E : Finset (Poly d)) (k : ℕ) (hXk : X.dimension = k)
    (hE : ∀ f ∈ E, f ∈ X.ideal) (x : Point d) (hx : x ∈ X.points)
    (hrank : Module.finrank ℂ (TrackD.jacKer E x) ≤ k) :
    X.tangentSpace x = TrackD.jacKer E x ∧
      Module.finrank ℂ (TrackD.jacKer E x) = k := by
  have hle := TrackD.tangent_le_jacKer X E hE x
  have hlo := TrackD.tangent_finrank_ge_dimension X hX x hx
  rw [hXk] at hlo
  have hmono := Submodule.finrank_mono hle
  have hdim : Module.finrank ℂ (X.tangentSpace x) = k := by omega
  have hdimE : Module.finrank ℂ (TrackD.jacKer E x) = k := by omega
  exact ⟨Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hdimE.symm), hdimE⟩

theorem physical_tangent_generic (X : AffineVariety d) (hX : X.IsIrreducible)
    (E : Finset (Poly d)) (g : Poly d) (k : ℕ) (hXk : X.dimension = k)
    (hE : ∀ f ∈ E, f ∈ X.ideal)
    (hg : ∃ x ∈ X.points, MvPolynomial.eval x g ≠ 0)
    (hrank : ∀ x : Point d, MvPolynomial.eval x g ≠ 0 →
      Module.finrank ℂ (TrackD.jacKer E x) ≤ k) :
    TrackD.ForGeneralPoint X (fun x =>
      X.tangentSpace x = TrackD.jacKer E x ∧
        Module.finrank ℂ (TrackD.jacKer E x) = k) := by
  refine ⟨g, hg, ?_⟩
  intro x hx hgn
  exact physical_tangent_eq_of_rank X hX E k hXk hE x hx (hrank x hgn)

theorem exists_secantSource_combination (E : Finset (Poly d))
    (R : Finset (AffineVariety d × AffineVariety d)) (D : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D)
    (hR : ∀ r ∈ R, ∃ p ∈ r.1.points, ∃ q ∈ r.2.points,
      q - p ∉ TrackD.jacKer E p) :
    ∃ g ∈ Submodule.span ℂ (E.image secantSourceTest : Set _),
      g.totalDegree ≤ D ∧ ∀ r ∈ R, ¬ TrackD.VanishesOnProduct g r.1 r.2 := by
  have hw (r : R) := hR r.val r.property
  choose p hp q hq hn using hw
  have htest (r : R) : ∃ f ∈ E.image secantSourceTest,
      MvPolynomial.eval (TrackD.pairPt (p r) (q r)) f ≠ 0 := by
    obtain ⟨f, hf, hfn⟩ := (secantSourceTest_nonzero_iff E _ _).mpr (hn r)
    exact ⟨secantSourceTest f, Finset.mem_image_of_mem _ hf, hfn⟩
  obtain ⟨g, hg, hgn⟩ := exists_polynomial_combination _ _ htest
  refine ⟨g, hg, polynomial_combination_degree _ D ?_ hg, ?_⟩
  · intro f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.mp hf
    exact (secantSourceTest_degree f₀).trans (hE f₀ hf₀)
  · intro r hr hzero
    let rr : R := ⟨r, hr⟩
    exact hgn rr (hzero (p rr) (hp rr) (q rr) (hq rr))

theorem exists_secantTarget_combination (E : Finset (Poly d))
    (R : Finset (AffineVariety d × AffineVariety d)) (D : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D)
    (hR : ∀ r ∈ R, ∃ p ∈ r.1.points, ∃ q ∈ r.2.points,
      q - p ∉ TrackD.jacKer E q) :
    ∃ g ∈ Submodule.span ℂ (E.image secantTargetTest : Set _),
      g.totalDegree ≤ D ∧ ∀ r ∈ R, ¬ TrackD.VanishesOnProduct g r.1 r.2 := by
  have hw (r : R) := hR r.val r.property
  choose p hp q hq hn using hw
  have htest (r : R) : ∃ f ∈ E.image secantTargetTest,
      MvPolynomial.eval (TrackD.pairPt (p r) (q r)) f ≠ 0 := by
    obtain ⟨f, hf, hfn⟩ := (secantTargetTest_nonzero_iff E _ _).mpr (hn r)
    exact ⟨secantTargetTest f, Finset.mem_image_of_mem _ hf, hfn⟩
  obtain ⟨g, hg, hgn⟩ := exists_polynomial_combination _ _ htest
  refine ⟨g, hg, polynomial_combination_degree _ D ?_ hg, ?_⟩
  · intro f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.mp hf
    exact (secantTargetTest_degree f₀).trans (hE f₀ hf₀)
  · intro r hr hzero
    let rr : R := ⟨r, hr⟩
    exact hgn rr (hzero (p rr) (hp rr) (q rr) (hq rr))

/-- Equations for the sum of a common kernel and the secant line. -/
def secantRow {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a b : V →ₗ[ℂ] ℂ) (v : V) : V →ₗ[ℂ] ℂ :=
  (a v) • b - (b v) • a

theorem secantRow_kernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (a : ι → V →ₗ[ℂ] ℂ) (v : V)
    (h : ∃ i, a i v ≠ 0) :
    (⨅ i, ⨅ j, LinearMap.ker (secantRow (a i) (a j) v)) =
      (⨅ i, LinearMap.ker (a i)) ⊔ (ℂ ∙ v) := by
  obtain ⟨i₀, hi₀⟩ := h
  ext w
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hw
    let c : ℂ := a i₀ w / a i₀ v
    have hker : w - c • v ∈ ⨅ i, LinearMap.ker (a i) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, map_sub, map_smul,
        smul_eq_mul]
      intro i
      have hr := hw i₀ i
      simp only [secantRow, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] at hr
      dsimp [c]
      field_simp [hi₀]
      linear_combination hr
    have hline : c • v ∈ ℂ ∙ v := Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
    have hs := Submodule.add_mem_sup hker hline
    simpa only [sub_add_cancel] using hs
  · intro hw
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    have hau (i : ι) : a i u = 0 := by
      exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hu i)
    intro i j
    simp only [secantRow, LinearMap.sub_apply, LinearMap.smul_apply,
      map_add, map_smul, smul_eq_mul, hau, zero_add]
    ring

def secantSourceRowPoly (f g : Poly d) (a : Fin d) : TrackD.PairPoly d :=
  secantSourceTest f * MvPolynomial.rename Sum.inl (MvPolynomial.pderiv a g) -
    secantSourceTest g * MvPolynomial.rename Sum.inl (MvPolynomial.pderiv a f)

def secantTargetRowPoly (f g : Poly d) (a : Fin d) : TrackD.PairPoly d :=
  secantTargetTest f * MvPolynomial.rename Sum.inr (MvPolynomial.pderiv a g) -
    secantTargetTest g * MvPolynomial.rename Sum.inr (MvPolynomial.pderiv a f)

theorem secantSourceRowPoly_eval (f g : Poly d) (p q w : Point d) :
    (∑ a : Fin d, MvPolynomial.eval (TrackD.pairPt p q)
      (secantSourceRowPoly f g a) * w a) =
      secantRow (differential f p) (differential g p) (q - p) w := by
  simp_rw [secantSourceRowPoly, map_sub, map_mul, secantSourceTest_eval,
    MvPolynomial.eval_rename]
  simp [secantRow, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, TrackD.pairPt, Function.comp_def,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem secantTargetRowPoly_eval (f g : Poly d) (p q w : Point d) :
    (∑ a : Fin d, MvPolynomial.eval (TrackD.pairPt p q)
      (secantTargetRowPoly f g a) * w a) =
      secantRow (differential f q) (differential g q) (q - p) w := by
  simp_rw [secantTargetRowPoly, map_sub, map_mul, secantTargetTest_eval,
    MvPolynomial.eval_rename]
  simp [secantRow, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, TrackD.pairPt, Function.comp_def,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

def combinedSecantMatrix (E : Finset (Poly d)) :
    Matrix (Bool × E × E) (Fin d) (TrackD.PairPoly d) :=
  fun r a => if r.1 then secantTargetRowPoly r.2.1 r.2.2 a
    else secantSourceRowPoly r.2.1 r.2.2 a

theorem combinedSecantMatrix_kernel (E : Finset (Poly d)) (p q : Point d)
    (hp : q - p ∉ TrackD.jacKer E p) (hq : q - p ∉ TrackD.jacKer E q) :
    LinearMap.ker ((combinedSecantMatrix E).map
      (MvPolynomial.eval (TrackD.pairPt p q))).mulVecLin =
      (TrackD.jacKer E p ⊔ (ℂ ∙ (q - p))) ⊓
        (TrackD.jacKer E q ⊔ (ℂ ∙ (q - p))) := by
  have hpk : (⨅ f : E, LinearMap.ker (differential f.val p)) = TrackD.jacKer E p := by
    ext w
    simp [TrackD.jacKer, Submodule.mem_iInf]
  have hqk : (⨅ f : E, LinearMap.ker (differential f.val q)) = TrackD.jacKer E q := by
    ext w
    simp [TrackD.jacKer, Submodule.mem_iInf]
  have hpe : ∃ f : E, differential f.val p (q - p) ≠ 0 := by
    obtain ⟨f, hf, hn⟩ := (secantSourceTest_nonzero_iff E p q).mpr hp
    exact ⟨⟨f, hf⟩, by simpa only [secantSourceTest_eval] using hn⟩
  have hqe : ∃ f : E, differential f.val q (q - p) ≠ 0 := by
    obtain ⟨f, hf, hn⟩ := (secantTargetTest_nonzero_iff E p q).mpr hq
    exact ⟨⟨f, hf⟩, by simpa only [secantTargetTest_eval] using hn⟩
  rw [← hpk, ← hqk, ← secantRow_kernel _ _ hpe, ← secantRow_kernel _ _ hqe]
  ext w
  simp only [LinearMap.mem_ker, Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · intro hw
    constructor
    · intro f g
      have hh := congrFun hw (false, f, g)
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, combinedSecantMatrix, secantSourceRowPoly_eval] using hh
    · intro f g
      have hh := congrFun hw (true, f, g)
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, combinedSecantMatrix, secantTargetRowPoly_eval] using hh
  · rintro ⟨hs, ht⟩
    funext r
    rcases r with ⟨side, f, g⟩
    cases side
    · simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, combinedSecantMatrix, secantSourceRowPoly_eval] using hs f g
    · simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, combinedSecantMatrix, secantTargetRowPoly_eval] using ht f g

def combinedSecantMinors (E : Finset (Poly d)) (c : ℕ) : Finset (TrackD.PairPoly d) :=
  Finset.univ.image fun rc : (Fin c ↪ Bool × E × E) × (Fin c ↪ Fin d) =>
    ((combinedSecantMatrix E).submatrix rc.1 rc.2).det

theorem combinedSecantMinors_unequal (E : Finset (Poly d)) (p q : Point d)
    (k : ℕ) (hkd : k ≤ d)
    (hp : q - p ∉ TrackD.jacKer E p) (hq : q - p ∉ TrackD.jacKer E q)
    (hpk : Module.finrank ℂ (TrackD.jacKer E p) = k)
    {g : TrackD.PairPoly d} (hg : g ∈ combinedSecantMinors E (d - k))
    (hgn : MvPolynomial.eval (TrackD.pairPt p q) g ≠ 0) :
    TrackD.jacKer E p ⊔ (ℂ ∙ (q - p)) ≠
      TrackD.jacKer E q ⊔ (ℂ ∙ (q - p)) := by
  obtain ⟨⟨rows, cols⟩, _, rfl⟩ := Finset.mem_image.mp hg
  let A := (combinedSecantMatrix E).map (MvPolynomial.eval (TrackD.pairPt p q))
  have hdet : (A.submatrix rows cols).det ≠ 0 := by
    rw [RingHom.map_det] at hgn
    exact hgn
  have hrank : d - k ≤ A.rank := by
    have h := Matrix.rank_submatrix_le A rows cols
    rwa [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrn' : A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) = d := by
    simpa [Matrix.rank] using hrn
  have hker := combinedSecantMatrix_kernel E p q hp hq
  intro heq
  have hdim : Module.finrank ℂ (LinearMap.ker A.mulVecLin) = k + 1 := by
    rw [hker, ← heq, inf_idem, Submodule.finrank_sup_span_singleton hp, hpk]
  omega

theorem combinedSecantMinors_exists (E : Finset (Poly d)) (p q : Point d)
    (k : ℕ) (hp : q - p ∉ TrackD.jacKer E p) (hq : q - p ∉ TrackD.jacKer E q)
    (hpk : Module.finrank ℂ (TrackD.jacKer E p) = k)
    (hqk : Module.finrank ℂ (TrackD.jacKer E q) = k)
    (hneq : TrackD.jacKer E p ⊔ (ℂ ∙ (q - p)) ≠
      TrackD.jacKer E q ⊔ (ℂ ∙ (q - p))) :
    ∃ g ∈ combinedSecantMinors E (d - k),
      MvPolynomial.eval (TrackD.pairPt p q) g ≠ 0 := by
  let A := (combinedSecantMatrix E).map (MvPolynomial.eval (TrackD.pairPt p q))
  have hkp : Module.finrank ℂ ↥(TrackD.jacKer E p ⊔ (ℂ ∙ (q - p))) = k + 1 := by
    rw [Submodule.finrank_sup_span_singleton hp, hpk]
  have hkq : Module.finrank ℂ ↥(TrackD.jacKer E q ⊔ (ℂ ∙ (q - p))) = k + 1 := by
    rw [Submodule.finrank_sup_span_singleton hq, hqk]
  have hlt : (TrackD.jacKer E p ⊔ (ℂ ∙ (q - p))) ⊓
      (TrackD.jacKer E q ⊔ (ℂ ∙ (q - p))) <
        TrackD.jacKer E p ⊔ (ℂ ∙ (q - p)) := by
    apply lt_of_le_of_ne inf_le_left
    intro heq
    have hle : TrackD.jacKer E p ⊔ (ℂ ∙ (q - p)) ≤
        TrackD.jacKer E q ⊔ (ℂ ∙ (q - p)) := by rw [← heq]; exact inf_le_right
    exact hneq (Submodule.eq_of_le_of_finrank_eq hle (hkp.trans hkq.symm))
  have hdimlt := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hkp, ← combinedSecantMatrix_kernel E p q hp hq] at hdimlt
  change Module.finrank ℂ (LinearMap.ker A.mulVecLin) < k + 1 at hdimlt
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrn' : A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) = d := by
    simpa [Matrix.rank] using hrn
  have hrank : d - k ≤ A.rank := by omega
  let e := Fintype.equivFin (Bool × E × E)
  let B := A.submatrix e.symm id
  have hBrank : B.rank = A.rank := by
    simpa [B] using Matrix.rank_submatrix A e.symm (Equiv.refl (Fin d))
  obtain ⟨rows, cols, hn⟩ := TrackA.regularity_matrix_le_rank_minor (q := d - k) B
    (by rw [hBrank]; exact hrank)
  let rows' : Fin (d - k) ↪ Bool × E × E := rows.trans e.symm.toEmbedding
  refine ⟨((combinedSecantMatrix E).submatrix rows' cols).det, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(rows', cols), Finset.mem_univ _, rfl⟩
  · rw [RingHom.map_det]
    exact hn

theorem combinedSecant_combination_unequal (E : Finset (Poly d)) (p q : Point d)
    (k : ℕ) (hkd : k ≤ d)
    (hp : q - p ∉ TrackD.jacKer E p) (hq : q - p ∉ TrackD.jacKer E q)
    (hpk : Module.finrank ℂ (TrackD.jacKer E p) = k)
    {g : TrackD.PairPoly d}
    (hg : g ∈ Submodule.span ℂ (combinedSecantMinors E (d - k) : Set _))
    (hgn : MvPolynomial.eval (TrackD.pairPt p q) g ≠ 0) :
    TrackD.jacKer E p ⊔ (ℂ ∙ (q - p)) ≠
      TrackD.jacKer E q ⊔ (ℂ ∙ (q - p)) := by
  obtain ⟨f, hf, hfn⟩ := polynomial_combination_nonzero _ _ hg hgn
  exact combinedSecantMinors_unequal E p q k hkd hp hq hpk hf hfn

theorem secantSourceRowPoly_degree (f g : Poly d) (D : ℕ)
    (hf : f.totalDegree ≤ D) (hg : g.totalDegree ≤ D) (a : Fin d) :
    (secantSourceRowPoly f g a).totalDegree ≤ 2 * D := by
  have hp (f : Poly d) (h : f.totalDegree ≤ D) :
      (MvPolynomial.rename (Sum.inl : Fin d → Fin d ⊕ Fin d)
        (MvPolynomial.pderiv a f)).totalDegree ≤ D := by
    apply (MvPolynomial.totalDegree_rename_le _ _).trans
    by_cases hz : MvPolynomial.pderiv a f = 0
    · simp [hz]
    · exact (OAI.QuarticPowerFree.pderiv_totalDegree_lt a f hz).le.trans h
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (by have := (secantSourceTest_degree f).trans hf; have := hp g hg; omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (by have := (secantSourceTest_degree g).trans hg; have := hp f hf; omega)

theorem secantTargetRowPoly_degree (f g : Poly d) (D : ℕ)
    (hf : f.totalDegree ≤ D) (hg : g.totalDegree ≤ D) (a : Fin d) :
    (secantTargetRowPoly f g a).totalDegree ≤ 2 * D := by
  have hp (f : Poly d) (h : f.totalDegree ≤ D) :
      (MvPolynomial.rename (Sum.inr : Fin d → Fin d ⊕ Fin d)
        (MvPolynomial.pderiv a f)).totalDegree ≤ D := by
    apply (MvPolynomial.totalDegree_rename_le _ _).trans
    by_cases hz : MvPolynomial.pderiv a f = 0
    · simp [hz]
    · exact (OAI.QuarticPowerFree.pderiv_totalDegree_lt a f hz).le.trans h
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (by have := (secantTargetTest_degree f).trans hf; have := hp g hg; omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (by have := (secantTargetTest_degree g).trans hg; have := hp f hf; omega)

theorem combinedSecantMinors_degree (E : Finset (Poly d)) (D c : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D) {g : TrackD.PairPoly d}
    (hg : g ∈ combinedSecantMinors E c) : g.totalDegree ≤ c * (2 * D) := by
  obtain ⟨⟨rows, cols⟩, _, rfl⟩ := Finset.mem_image.mp hg
  let Q := (combinedSecantMatrix E).submatrix rows cols
  let Q' : Matrix (Fin c) (Fin c) (Poly (d + d)) :=
    Q.map (MvPolynomial.rename finSumFinEquiv)
  have hQ : ∀ i j, (Q' i j).totalDegree ≤ 2 * D := by
    intro i j
    apply (MvPolynomial.totalDegree_rename_le _ _).trans
    dsimp [Q, Matrix.submatrix, combinedSecantMatrix]
    split_ifs
    · exact secantTargetRowPoly_degree _ _ D (hE _ (rows i).2.1.property)
        (hE _ (rows i).2.2.property) _
    · exact secantSourceRowPoly_degree _ _ D (hE _ (rows i).2.1.property)
        (hE _ (rows i).2.2.property) _
  have hdeg := TrackA.polynomial_matrix_det_degree_le Q' (2 * D) hQ
  have hmap : Q'.det = MvPolynomial.rename finSumFinEquiv Q.det := by
    exact (RingHom.map_det _ _).symm
  rw [hmap] at hdeg
  have hren : (MvPolynomial.rename finSumFinEquiv Q.det).totalDegree = Q.det.totalDegree :=
    MvPolynomial.totalDegree_renameEquiv finSumFinEquiv Q.det
  rw [hren] at hdeg
  exact hdeg

theorem combinedSecantMinors_nonvanish_on_product (E : Finset (Poly d))
    (X Y : AffineVariety d) (k : ℕ) (hk : 1 ≤ k)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXk : X.dimension = k) (hYk : Y.dimension = k)
    (htr : TrackD.GenericallyTransverse X Y)
    (hpeq : TrackD.ForGeneralPoint X (fun p =>
      X.tangentSpace p = TrackD.jacKer E p ∧
        Module.finrank ℂ (TrackD.jacKer E p) = k))
    (hqeq : TrackD.ForGeneralPoint Y (fun q =>
      Y.tangentSpace q = TrackD.jacKer E q ∧
        Module.finrank ℂ (TrackD.jacKer E q) = k))
    (hspan : ¬ ∃ Ff : AffineSubspace ℂ (Point d),
      Module.finrank ℂ Ff.direction ≤ k + 1 ∧ X.points ⊆ ↑Ff) :
    ∃ g ∈ combinedSecantMinors E (d - k), ¬ TrackD.VanishesOnProduct g X Y := by
  obtain ⟨p₀, hp₀, q₀, hq₀, _⟩ := htr.exists
  have hdata := (htr.and hX hY (hpeq.on_left ⟨q₀, hq₀⟩)).and
    hX hY (hqeq.on_right ⟨p₀, hp₀⟩)
  have hex : ∃ p ∈ X.points, ∃ q ∈ Y.points,
      (q - p ∉ X.tangentSpace p ∧ q - p ∉ Y.tangentSpace q) ∧
      (X.tangentSpace p = TrackD.jacKer E p ∧
        Module.finrank ℂ (TrackD.jacKer E p) = k) ∧
      (Y.tangentSpace q = TrackD.jacKer E q ∧
        Module.finrank ℂ (TrackD.jacKer E q) = k) ∧
      X.tangentSpace p ⊔ (ℂ ∙ (q - p)) ≠ Y.tangentSpace q ⊔ (ℂ ∙ (q - p)) := by
    by_contra hn
    push_neg at hn
    have heq : TrackD.ForGeneralPair X Y (fun p q =>
        X.tangentSpace p ⊔ (ℂ ∙ (q - p)) = Y.tangentSpace q ⊔ (ℂ ∙ (q - p))) := by
      apply hdata.mono
      intro p hp q hq hh
      exact hn p hp q hq hh.1.1 hh.1.2 hh.2
    obtain ⟨Ff, hFf, hXFf, _⟩ := TrackD.geo_secants_equal_tangents
      X Y k hX hY hXk hYk hk htr heq
    exact hspan ⟨Ff, hFf, hXFf⟩
  obtain ⟨p, hp, q, hq, htrpq, hpeq, hqeq, hneq⟩ := hex
  rw [hpeq.1, hqeq.1] at htrpq hneq
  obtain ⟨g, hg, hgn⟩ := combinedSecantMinors_exists E p q k
    htrpq.1 htrpq.2 hpeq.2 hqeq.2 hneq
  exact ⟨g, hg, fun hzero => hgn (hzero p hp q hq)⟩

def jacobianMinorTests (E : List (Poly d)) (c : ℕ) : Finset (Poly d) :=
  Finset.univ.image fun rc : (Fin c ↪ Fin E.length) × (Fin c ↪ Fin d) =>
    ((TrackA.jacobian E).submatrix rc.1 rc.2).det

theorem jacobianMinorTests_coe (E : List (Poly d)) (c : ℕ) :
    (jacobianMinorTests E c : Set (Poly d)) = TrackA.jacobianMinors E c := by
  ext f
  simp [jacobianMinorTests, TrackA.jacobianMinors, eq_comm]

theorem finite_jacobian_rank_test (E : List (Poly d)) (k : ℕ) (hk : k ≤ d)
    (Z : Finset (Point d))
    (hZ : ∀ z ∈ Z, Module.finrank ℂ (TrackD.jacKer E.toFinset z) = k) :
    ∃ g : Poly d, (∀ z ∈ Z, MvPolynomial.eval z g ≠ 0) ∧
      ∀ z : Point d, MvPolynomial.eval z g ≠ 0 →
        Module.finrank ℂ (TrackD.jacKer E.toFinset z) ≤ k := by
  have hw (z : Z) : ∃ f ∈ jacobianMinorTests E (d - k), MvPolynomial.eval z.val f ≠ 0 := by
    let A := TrackD.evaluatedJacobian E z.val
    have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [TrackD.evaluatedJacobian_kernel, hZ z.val z.property] at hrn
    have hrank : A.rank = d - k := by
      have hh : A.rank + k = d := by simpa [Matrix.rank] using hrn
      omega
    obtain ⟨rows, cols, hn⟩ := TrackA.matrix_rank_minor A hrank
    refine ⟨((TrackA.jacobian E).submatrix rows cols).det, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(rows, cols), Finset.mem_univ _, rfl⟩
    · rw [RingHom.map_det]
      exact hn
  obtain ⟨g, hg, hgn⟩ := exists_polynomial_combination
    (jacobianMinorTests E (d - k)) (fun z : Z => z.val) hw
  have hg' : g ∈ Submodule.span ℂ (TrackA.jacobianMinors E (d - k)) := by
    rw [← jacobianMinorTests_coe]
    exact hg
  refine ⟨g, fun z hz => hgn ⟨z, hz⟩, ?_⟩
  intro z hn
  have hrank := TrackD.minor_certificate_finrank E (d - k) g hg' z hn
  omega

/-- Clearing a label polynomial needs no degree estimate for the frozen 191 conclusion. -/
theorem label_clear_exists (i₀ : Fin d) (G : TrackD.PairPoly d) :
    ∃ (N : ℕ) (H : TrackD.PairPoly d), ∀ p q : Point d, (q - p) i₀ ≠ 0 →
      MvPolynomial.eval (TrackD.pairPt p q) H =
        ((q - p) i₀) ^ N * MvPolynomial.eval (TrackD.labelPt i₀ p q) G := by
  let δ : TrackD.PairPoly d := MvPolynomial.X (Sum.inr i₀) - MvPolynomial.X (Sum.inl i₀)
  have hδ (p q : Point d) : MvPolynomial.eval (TrackD.pairPt p q) δ = (q - p) i₀ := by
    simp [δ, TrackD.pairPt]
  induction G using MvPolynomial.induction_on with
  | C c =>
    exact ⟨0, MvPolynomial.C c, by intros; simp⟩
  | add f g hf hg =>
    obtain ⟨Nf, Hf, hf⟩ := hf
    obtain ⟨Ng, Hg, hg⟩ := hg
    refine ⟨Nf + Ng, δ ^ Ng * Hf + δ ^ Nf * Hg, ?_⟩
    intro p q hc
    simp only [map_add, map_mul, map_pow, hδ, hf p q hc, hg p q hc, pow_add]
    ring
  | mul_X f i hf =>
    obtain ⟨N, H, hf⟩ := hf
    cases i with
    | inl a =>
      refine ⟨N, H * MvPolynomial.X (Sum.inl a), ?_⟩
      intro p q hc
      simp only [map_mul, MvPolynomial.eval_X]
      rw [hf p q hc]
      simp only [TrackD.pairPt, TrackD.labelPt, Sum.elim_inl]
      ring
    | inr a =>
      refine ⟨N + 1, H *
        (MvPolynomial.X (Sum.inr a) - MvPolynomial.X (Sum.inl a)), ?_⟩
      intro p q hc
      simp only [map_mul, map_sub, MvPolynomial.eval_X]
      rw [hf p q hc]
      simp only [
        TrackD.pairPt, TrackD.labelPt, Sum.elim_inl, Sum.elim_inr,
        TrackD.dirChart, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
        pow_succ, Pi.sub_apply]
      have hc' : q i₀ - p i₀ ≠ 0 := hc
      field_simp [hc'] <;> ring

/-- Nonvanishing of finitely many factors persists on an irreducible product. -/
theorem pair_product_nonvanish (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) (f g : TrackD.PairPoly d)
    (hf : ¬ TrackD.VanishesOnProduct f X Y)
    (hg : ¬ TrackD.VanishesOnProduct g X Y) :
    ¬ TrackD.VanishesOnProduct (f * g) X Y := by
  have hopen (a : TrackD.PairPoly d) (ha : ¬ TrackD.VanishesOnProduct a X Y) :
      TrackD.ForGeneralPair X Y (fun p q => MvPolynomial.eval (TrackD.pairPt p q) a ≠ 0) := by
    refine ⟨a, ?_, fun _ _ _ _ hn => hn⟩
    by_contra hn
    apply ha
    push Not at hn
    exact hn
  obtain ⟨p, hp, q, hq, hfn, hgn⟩ := ((hopen f hf).and hX hY (hopen g hg)).exists
  intro hzero
  exact mul_ne_zero hfn hgn (by simpa only [map_mul] using hzero p hp q hq)

/-- A single linear combination detects a minor on each of the finite products. -/
theorem exists_combinedSecant_combination (E : Finset (Poly d))
    (R : Finset (AffineVariety d × AffineVariety d)) (D c : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D)
    (hR : ∀ r ∈ R, ∃ g ∈ combinedSecantMinors E c,
      ¬ TrackD.VanishesOnProduct g r.1 r.2) :
    ∃ g ∈ Submodule.span ℂ (combinedSecantMinors E c : Set _),
      g.totalDegree ≤ c * (2 * D) ∧
      ∀ r ∈ R, ¬ TrackD.VanishesOnProduct g r.1 r.2 := by
  have hw (r : R) : ∃ p ∈ r.val.1.points, ∃ q ∈ r.val.2.points,
      ∃ g ∈ combinedSecantMinors E c, MvPolynomial.eval (TrackD.pairPt p q) g ≠ 0 := by
    obtain ⟨g, hg, hn⟩ := hR r.val r.property
    have hex : ∃ p ∈ r.val.1.points, ∃ q ∈ r.val.2.points,
        MvPolynomial.eval (TrackD.pairPt p q) g ≠ 0 := by
      by_contra hh
      apply hn
      push Not at hh
      exact hh
    obtain ⟨p, hp, q, hq, hgn⟩ := hex
    exact ⟨p, hp, q, hq, g, hg, hgn⟩
  choose p hp q hq hnon using hw
  obtain ⟨g, hg, hgn⟩ := exists_polynomial_combination
    (combinedSecantMinors E c) (fun r : R => TrackD.pairPt (p r) (q r)) hnon
  refine ⟨g, hg, polynomial_combination_degree _ (c * (2 * D))
    (fun _ hf => combinedSecantMinors_degree E D c hE hf) hg, ?_⟩
  intro r hr hzero
  let rr : R := ⟨r, hr⟩
  exact hgn rr (hzero (p rr) (hp rr) (q rr) (hq rr))

/-- Choose all three physical tests simultaneously on a finite carrier family. -/
theorem exists_physical_pair_tests (E : Finset (Poly d)) (D k : ℕ)
    (R : Finset (AffineVariety d × AffineVariety d)) (hk : 1 ≤ k)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D)
    (hR : ∀ r ∈ R, r.1.IsIrreducible ∧ r.2.IsIrreducible ∧
      r.1.dimension = k ∧ r.2.dimension = k)
    (htr : ∀ r ∈ R, TrackD.GenericallyTransverse r.1 r.2)
    (hp : ∀ r ∈ R, TrackD.ForGeneralPoint r.1 (fun p =>
      r.1.tangentSpace p = TrackD.jacKer E p ∧ Module.finrank ℂ (TrackD.jacKer E p) = k))
    (hq : ∀ r ∈ R, TrackD.ForGeneralPoint r.2 (fun q =>
      r.2.tangentSpace q = TrackD.jacKer E q ∧ Module.finrank ℂ (TrackD.jacKer E q) = k))
    (hspan : 2 ≤ k → ∀ r ∈ R, ¬ ∃ Ff : AffineSubspace ℂ (Point d),
      Module.finrank ℂ Ff.direction ≤ k + 1 ∧ r.1.points ⊆ ↑Ff) :
    ∃ fs ft fm : TrackD.PairPoly d,
      fs ∈ Submodule.span ℂ (E.image secantSourceTest : Set _) ∧
      ft ∈ Submodule.span ℂ (E.image secantTargetTest : Set _) ∧
      (2 ≤ k → fm ∈ Submodule.span ℂ (combinedSecantMinors E (d - k) : Set _)) ∧
      (fs * ft * fm).totalDegree ≤ (2 * d + 2) * D ∧
      ∀ r ∈ R, ¬ TrackD.VanishesOnProduct (fs * ft * fm) r.1 r.2 := by
  have htrans (r : AffineVariety d × AffineVariety d) (hr : r ∈ R) :
      ∃ p ∈ r.1.points, ∃ q ∈ r.2.points,
        q - p ∉ TrackD.jacKer E p ∧ q - p ∉ TrackD.jacKer E q := by
    obtain ⟨p₀, hp₀, q₀, hq₀, _⟩ := (htr r hr).exists
    have hh := ((htr r hr).and (hR r hr).1 (hR r hr).2.1
      ((hp r hr).on_left ⟨q₀, hq₀⟩)).and (hR r hr).1 (hR r hr).2.1
      ((hq r hr).on_right ⟨p₀, hp₀⟩)
    obtain ⟨p, hpp, q, hqq, hdata⟩ := hh.exists
    have ht := hdata.1.1
    rw [hdata.1.2.1, hdata.2.1] at ht
    exact ⟨p, hpp, q, hqq, ht⟩
  obtain ⟨fs, hfs, hfsdeg, hfsn⟩ := exists_secantSource_combination E R D hE (by
    intro r hr
    obtain ⟨p, hpp, q, hqq, hn⟩ := htrans r hr
    exact ⟨p, hpp, q, hqq, hn.1⟩)
  obtain ⟨ft, hft, hftdeg, hftn⟩ := exists_secantTarget_combination E R D hE (by
    intro r hr
    obtain ⟨p, hpp, q, hqq, hn⟩ := htrans r hr
    exact ⟨p, hpp, q, hqq, hn.2⟩)
  have hminor : ∃ fm : TrackD.PairPoly d,
      (2 ≤ k → fm ∈ Submodule.span ℂ (combinedSecantMinors E (d - k) : Set _)) ∧
      fm.totalDegree ≤ (d - k) * (2 * D) ∧
      ∀ r ∈ R, ¬ TrackD.VanishesOnProduct fm r.1 r.2 := by
    by_cases hk2 : 2 ≤ k
    · obtain ⟨fm, hfm, hfmdeg, hfmn⟩ := exists_combinedSecant_combination E R D (d - k) hE (by
        intro r hr
        exact combinedSecantMinors_nonvanish_on_product E r.1 r.2 k hk
          (hR r hr).1 (hR r hr).2.1 (hR r hr).2.2.1 (hR r hr).2.2.2
          (htr r hr) (hp r hr) (hq r hr) (hspan hk2 r hr))
      exact ⟨fm, fun _ => hfm, hfmdeg, hfmn⟩
    · refine ⟨1, fun h => False.elim (hk2 h), by simp, ?_⟩
      intro r hr hzero
      obtain ⟨p, hpp, q, hqq, _⟩ := (htr r hr).exists
      have hh := hzero p hpp q hqq
      simpa only [map_one, one_ne_zero] using hh
  obtain ⟨fm, hfm, hfmdeg, hfmn⟩ := hminor
  refine ⟨fs, ft, fm, hfs, hft, hfm, ?_, ?_⟩
  · calc (fs * ft * fm).totalDegree
        ≤ fs.totalDegree + ft.totalDegree + fm.totalDegree := by
          exact (MvPolynomial.totalDegree_mul _ _).trans
            (Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _)
      _ ≤ D + D + (d - k) * (2 * D) := by omega
      _ = (2 + (d - k) * 2) * D := by ring
      _ ≤ (2 * d + 2) * D := Nat.mul_le_mul_right D (by omega)
  · intro r hr
    exact pair_product_nonvanish r.1 r.2 (hR r hr).1 (hR r hr).2.1 _ _
      (pair_product_nonvanish r.1 r.2 (hR r hr).1 (hR r hr).2.1 _ _ (hfsn r hr) (hftn r hr))
      (hfmn r hr)

open Filter

/-- Equal-width selected pools use identical roles or disjoint point sets. -/
theorem common_pool_roles_equal_or_disjoint {regime : Regime d}
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (M : CommonPoolProfile T) (i : ℕ) :
    T.sources i = T.targets i ∨
      Disjoint (TrackD.poolPts (T.sources i)) (TrackD.poolPts (T.targets i)) := by
  rcases (T.certificate i).window with hcommon | hseparated | houter
  · obtain ⟨X, Y, hX, hY, _, _⟩ := hcommon
    by_cases hXY : X = Y
    · left
      rw [hX, hY, hXY]
    · right
      have hx : X ∈ T.sources i := by simp [hX]
      have hy : Y ∈ T.targets i := by simp [hY]
      have hdis := (T.certificate i).good.pieces_disjoint
        ((T.certificate i).sources_subset hx) ((T.certificate i).targets_subset hy) hXY
      simpa [TrackD.poolPts, hX, hY] using hdis
  · obtain ⟨X, Y, hX, hY, hsep, _, _⟩ := hseparated
    have hx : X ∈ T.sources i := by simp [hX]
    have hy : Y ∈ T.targets i := by simp [hY]
    have hxw := M.width i X (Finset.mem_union_left _ hx)
    have hyw := M.width i Y (Finset.mem_union_right _ hy)
    rw [hxw, hyw] at hsep
    have htol : selectionTolerance (T.precision i) < 1 := by
      unfold selectionTolerance
      apply (div_lt_one₀ (by positivity)).mpr
      have hh : 0 ≤ (T.precision i : ℝ) := Nat.cast_nonneg _
      linarith
    have hh := mul_lt_mul_of_pos_right htol (M.width_pos i)
    rcases hsep with hsep | hsep <;> norm_num at hh <;> linarith
  · exact Or.inl houter.1

/-- Uniform pair testing uses the original source pool in both roles. -/
theorem common_source_product_testing {regime : Regime d}
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (M : CommonPoolProfile T) (j : ℕ) (hj : j < d) (τ ξ : ℝ)
    (W : CommonPhysicalSequence T M j τ) (hτ : -1 < τ) (hξ : 0 < ξ)
    (hplateau : TrackD.OnPlateau M.b j ξ τ)
    (θ K : ℝ) (hθ : 0 < θ) (hK : 1 ≤ K) :
    ∀ᶠ i in atTop, ∀ g : TrackD.PairPoly d,
      (g.totalDegree : ℝ) ≤ K * TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ →
      (((TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.sources i)).filter (fun pq =>
        MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2)) g = 0 ∧
        ¬ TrackD.VanishesOnProduct g (W.owner i pq.1) (W.owner i pq.2))).card : ℝ) ≤
        θ * ((TrackD.poolPts (T.sources i)).card : ℝ) ^ 2 := by
  obtain ⟨θ₁, hθ₁, η, hη, _, ρ₀, hρ₀, s₁, hproduct⟩ :=
    TrackD.prof_product_testing_with_margin d regime.dimension_ge_three θ hθ ξ hξ K hK
  filter_upwards [M.good θ₁ hθ₁ η hη 1 le_rfl (ρ₀ / 2) (by positivity),
    M.width_grows.eventually_ge_atTop s₁, common_physical_test_degree_one M τ hτ]
    with i hpool hs hT
  intro g hg
  have hsource : TrackD.CarrierAssignment (T.sources i) j (W.owner i) := by
    intro X hX q hq
    exact W.supported i X (Finset.mem_union_left _ hX) q hq
  have hh := hproduct (regime.P i) (T.sources i) (T.sources i) (M.s i)
    (ρ₀ / 2) M.b (by linarith) hpool.1 hpool.1 hs j hj τ hplateau hT
    (W.owner i) (W.owner i) hsource hsource g hg
  simpa only [pow_two, mul_assoc] using hh

end
end DistinctDistances.SparseCones
