import DistinctDistances.TrackD.Profiles.Budget
import DistinctDistances.TrackD.Profiles.PoolFamilies

/-!
# `prof:regularity` and `prof:product-testing` (`profiles.tex:340–511`)

Consumers: `sparse-cones.tex:99–125` (common equations, `g_ph`), 216–316, 426–562, 697–781,
795–928; `depth.tex:103–150, 230–262`.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

variable {d : ℕ}

/-- `prof:regularity.component` (`profiles.tex:361–368`): every local carrier at a point of a
proper path is an irreducible component of the path locus (a minimal prime of the cut system), of
dimension `d - j`; larger components elsewhere are allowed. Stated for the record that consumers
use: membership in `IsCarrier` *is* componenthood, and local purity is `prof_partition_pure`. -/
theorem prof_regularity_component (X : Piece d) (j : ℕ) (Z : AffineVariety d)
    (hZ : X.path.IsCarrier j Z) : Z.IsIrreducible ∧ Z.ideal ∈ (X.path.system j).minimalPrimes :=
  ⟨hZ.isPrime, hZ⟩

/-- Regularity of a point with respect to a pool's common equations `F` and minor test `g_ph`
(`profiles.tex:345–349`): `g_ph` is nonzero, the point lies on a unique carrier of the pool, which
is smooth there with tangent space the Jacobian kernel of `F`. -/
def JacRegularAt (pl : Finset (Piece d)) (j : ℕ) (F : Finset (Poly d)) (gph : Poly d)
    (y : Point d) : Prop :=
  MvPolynomial.eval y gph ≠ 0 ∧
    ∃ Z : AffineVariety d, (PoolCarrier pl j Z ∧ y ∈ Z) ∧
      (∀ Z' : AffineVariety d, PoolCarrier pl j Z' ∧ y ∈ Z' → Z' = Z) ∧
      Z.IsSmoothAt y ∧ Z.tangentSpace y = jacKer F y

theorem familyJacRegularAt_iff (pl : Finset (Piece d)) (j : ℕ)
    (E : List (Poly d)) (g : Poly d) (y : Point d) :
    FamilyJacRegularAt (poolCarrierFamily pl j) E g y ↔
      JacRegularAt pl j E.toFinset g y := by
  simp only [FamilyJacRegularAt, JacRegularAt, mem_poolCarrierFamily]

/-- The geometric and per-piece counting assembly of `prof:regularity.jacobian`.
The exceptional mass and proper-cut bounds are measured on each original piece. -/
theorem jacobian_pool_certificate (P : Finset (Pt d)) (pl : Finset (Piece d))
    (θ ξ K : ℝ) (hpl : ∀ X ∈ pl, PieceGood P θ ξ K X)
    (j : ℕ) (hj : j ≤ d) (T : ℝ) (E : List (Poly d)) (g : Poly d)
    (bad : AffineFamily.Family d)
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus (poolCarrierFamily pl j)).ideal ∧
      (f.totalDegree : ℝ) ≤ T)
    (hgdeg : (g.totalDegree : ℝ) ≤ T)
    (hg : g ∈ Submodule.span ℂ (TrackA.jacobianMinors E j))
    (hproper : ∀ Z ∈ poolCarrierFamily pl j, Z ∉ bad → g ∉ Z.ideal)
    (hunique : ∀ y : Point d, MvPolynomial.eval y g ≠ 0 →
      ∀ Z ∈ poolCarrierFamily pl j, ∀ Z' ∈ poolCarrierFamily pl j,
        y ∈ Z → y ∈ Z' → Z = Z')
    (δ ε : ℝ)
    (hbad : ∀ X ∈ pl, ((X.pts.filter (fun x =>
      ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad)).card : ℝ) ≤ δ * X.pts.card)
    (hcuts : ∀ X ∈ pl, ((X.pts.filter (fun x =>
      ∃ Z ∈ X.path.localCarriers j (toC x),
        g ∉ Z.ideal ∧ MvPolynomial.eval (toC x) g = 0)).card : ℝ) ≤ ε * X.pts.card) :
    (∀ f ∈ E.toFinset, (f.totalDegree : ℝ) ≤ T) ∧
      (g.totalDegree : ℝ) ≤ T ∧
      (∀ Z, PoolCarrier pl j Z → ∀ f ∈ E.toFinset, f ∈ Z.ideal) ∧
      (∀ y : Point d, MvPolynomial.eval y g ≠ 0 →
        Module.finrank ℂ (jacKer E.toFinset y) + j ≤ d) ∧
      ∀ X ∈ pl, ((X.pts.filter (fun x =>
        ¬ JacRegularAt pl j E.toFinset g (toC x))).card : ℝ) ≤ (δ + ε) * X.pts.card := by
  have hmem := pool_family_equations pl j E (fun f hf => (hE f hf).1)
  refine ⟨(fun f hf => (hE f (List.mem_toFinset.mp hf)).2), hgdeg,
    (fun Z hZ f hf => hmem Z hZ f (List.mem_toFinset.mp hf)),
    (fun y hy => minor_certificate_finrank E j g hg y hy), ?_⟩
  intro X hX
  have hcount := jacobian_bad_points_accounting X j hj ((hpl X hX).vanish)
    (poolCarrierFamily pl j) bad E g (by
      intro x hx Z hZ
      exact (mem_poolCarrierFamily pl j Z).mpr ⟨X, hX, hZ.1, x, hx, hZ.2⟩)
    (poolCarrierFamily_pure P pl θ ξ K hpl j hj)
    (fun Z hZ => hmem Z ((mem_poolCarrierFamily pl j Z).mp hZ))
    hg hproper hunique δ ε (hbad X hX) (hcuts X hX)
  simpa only [familyJacRegularAt_iff] using hcount

/-- A polynomial vanishing on a real affine subspace vanishes on its complex affine span. -/
private theorem dnonreal_vanishing_on_affineSpan (G : AffineSubspace ℝ (Pt d))
    (x₀ : Pt d) (hx₀ : x₀ ∈ G) (f : Poly d)
    (hvan : ∀ x ∈ G, MvPolynomial.eval (toC x) f = 0)
    (z : Point d) (hz : z ∈ affineSpan ℂ (toC '' (G : Set (Pt d)))) :
    MvPolynomial.eval z f = 0 := by
  classical
  let T : Set (Point d) := toC '' (G : Set (Pt d))
  let S : Set (Point d) := (fun y : Point d => y -ᵥ toC x₀) '' T
  let r : ℕ := Module.finrank ℂ (Submodule.span ℂ S)
  obtain ⟨v, hvS, hvspan, _⟩ :
      ∃ v : Fin r → Point d, (∀ i, v i ∈ S) ∧
        Submodule.span ℂ (Set.range v) = Submodule.span ℂ S ∧ LinearIndependent ℂ v := by
    simpa [r] using Submodule.exists_fun_fin_finrank_span_eq ℂ S
  have hx₀T : toC x₀ ∈ T := Set.mem_image_of_mem toC hx₀
  have hdir : (affineSpan ℂ T).direction = Submodule.span ℂ (Set.range v) := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℂ hx₀T]
    exact hvspan.symm
  have hvWitness : ∀ i, ∃ x : Pt d, x ∈ G ∧ toC x -ᵥ toC x₀ = v i := by
    intro i
    rcases hvS i with ⟨y, hy, hyv⟩
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    simpa [hxy] using hyv
  choose x hxG hvx using hvWitness
  have hvxC (i : Fin r) : v i = toC (x i -ᵥ x₀) := by
    rw [← hvx i]
    ext j
    simp [toC]
  let param : Fin d → MvPolynomial (Fin r) ℂ := fun j =>
    MvPolynomial.C (toC x₀ j) +
      ∑ i, MvPolynomial.C (v i j) * MvPolynomial.X i
  let q : MvPolynomial (Fin r) ℂ := MvPolynomial.aeval param f
  have hEval (u : Fin r → ℂ) :
      MvPolynomial.eval u q =
        MvPolynomial.eval (fun j => toC x₀ j + ∑ i, u i * v i j) f := by
    have hcomp : (MvPolynomial.aeval u).comp (MvPolynomial.aeval param) =
        MvPolynomial.aeval (fun j => toC x₀ j + ∑ i, u i * v i j) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [param, mul_comm]
    simpa [q] using congrArg (fun φ : Poly d →ₐ[ℂ] ℂ => φ f) hcomp
  have hrealPoint (u : Fin r → ℝ) :
      (fun j => toC x₀ j + ∑ i, (u i : ℂ) * v i j) =
        toC ((∑ i, u i • (x i -ᵥ x₀)) +ᵥ x₀) := by
    funext j
    simp [toC, hvxC, Finset.sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    <;> ring
  have hpointG (u : Fin r → ℝ) :
      (∑ i, u i • (x i -ᵥ x₀)) +ᵥ x₀ ∈ G := by
    apply AffineSubspace.vadd_mem_of_mem_direction
    · exact Submodule.sum_mem _ fun i hi =>
        G.direction.smul_mem _ (AffineSubspace.vsub_mem_direction (hxG i) hx₀)
    · exact hx₀
  have hqzero : q = 0 := by
    apply MvPolynomial.funext_set
      (s := fun _ : Fin r => Set.range (fun t : ℝ => (t : ℂ)))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro u hu
    have hucoord : ∀ i, u i ∈ Set.range (fun t : ℝ => (t : ℂ)) := by
      intro i
      exact (Set.mem_pi.mp hu) i (Set.mem_univ i)
    choose t ht using hucoord
    have huEq : u = fun i => (t i : ℂ) := by
      funext i
      exact (ht i).symm
    rw [huEq, hEval, hrealPoint]
    exact hvan _ (hpointG t)
  have hzdir : z -ᵥ toC x₀ ∈ Submodule.span ℂ (Set.range v) := by
    rw [← hdir]
    exact AffineSubspace.vsub_mem_direction hz (subset_affineSpan ℂ T hx₀T)
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzdir
  have hqu : MvPolynomial.eval u q = 0 := by rw [hqzero]; simp
  rw [hEval] at hqu
  have hzEq : z = fun j => toC x₀ j + ∑ i, u i * v i j := by
    calc
      z = (z -ᵥ toC x₀) +ᵥ toC x₀ := by simp
      _ = (∑ i, u i • v i) +ᵥ toC x₀ := by rw [hu]
      _ = _ := by
        ext j
        simp [Finset.sum_apply, smul_eq_mul]
        ring
  rw [hzEq]
  exact hqu

private def dnonrealAffineLinearPoly (L : Point d →ₗ[ℂ] ℂ) (a : Point d) : Poly d :=
  (∑ i : Fin d, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i) -
    MvPolynomial.C (L a)

private theorem dnonrealAffineLinearPoly_degree (L : Point d →ₗ[ℂ] ℂ) (a : Point d) :
    (dnonrealAffineLinearPoly L a).totalDegree ≤ 1 := by
  classical
  have hsum :
      (∑ i : Fin d, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    calc
      _ ≤ (MvPolynomial.C (L (Pi.single i 1))).totalDegree +
          (MvPolynomial.X i : Poly d).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp
  unfold dnonrealAffineLinearPoly
  rw [sub_eq_add_neg]
  calc
    _ ≤ max _ _ := MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := max_le hsum (by simp)

private theorem dnonrealAffineLinearPoly_eval (L : Point d →ₗ[ℂ] ℂ) (a y : Point d) :
    MvPolynomial.eval y (dnonrealAffineLinearPoly L a) = L (y -ᵥ a) := by
  classical
  have hy : y = ∑ i : Fin d, y i • (Pi.single i (1 : ℂ) : Point d) := by
    ext j
    simp [Pi.single_apply]
  unfold dnonrealAffineLinearPoly
  rw [MvPolynomial.eval_sub]
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  have hlin :
      (∑ i : Fin d, L (Pi.single i (1 : ℂ)) * y i) = L y := by
    calc
      _ = ∑ i : Fin d, L (y i • (Pi.single i (1 : ℂ) : Point d)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [map_smul, mul_comm]
      _ = L (∑ i : Fin d, y i • (Pi.single i (1 : ℂ) : Point d)) := by rw [map_sum]
      _ = L y := congrArg L hy.symm
  rw [vsub_eq_sub, map_sub, hlin]

/-- A nonreal affine flat with a real point has a proper degree-one cut containing all its real
points. The density helper above identifies the complex affine span of the real locus with its
Zariski closure. -/
private theorem dnonreal_affine_separator (Z : AffineVariety d) (hflat : IsFlat Z)
    (hnonreal : ¬ IsRealFlat Z) (hne : ∃ x : Pt d, toC x ∈ Z) :
    ∃ f : Poly d, f.totalDegree ≤ 1 ∧
      (∀ x : Pt d, toC x ∈ Z → MvPolynomial.eval (toC x) f = 0) ∧
      ∃ z ∈ Z, MvPolynomial.eval z f ≠ 0 := by
  classical
  obtain ⟨F, hF⟩ := hflat
  rcases hne with ⟨x₀, hx₀Z⟩
  have hx₀F : toC x₀ ∈ F := by
    change toC x₀ ∈ Z.points at hx₀Z
    rw [hF] at hx₀Z
    exact hx₀Z
  let G : AffineSubspace ℝ (Pt d) :=
    { carrier := {x | toC x ∈ F}
      smul_vsub_vadd_mem' := by
        rintro t p₁ p₂ p₃ hp₁ hp₂ hp₃
        change toC p₁ ∈ F at hp₁
        change toC p₂ ∈ F at hp₂
        change toC p₃ ∈ F at hp₃
        have ht := F.smul_vsub_vadd_mem' (t : ℂ) hp₁ hp₂ hp₃
        change toC (t • (p₁ -ᵥ p₂) +ᵥ p₃) ∈ F
        have hmap : toC (t • (p₁ -ᵥ p₂) +ᵥ p₃) =
            (t : ℂ) • (toC p₁ -ᵥ toC p₂) +ᵥ toC p₃ := by
          ext i
          simp [toC, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub]
        rw [hmap]
        exact ht }
  have hGmem (x : Pt d) : x ∈ G ↔ toC x ∈ F := Iff.rfl
  have hx₀G : x₀ ∈ G := hGmem x₀ |>.2 hx₀F
  let T : Set (Point d) := toC '' (G : Set (Pt d))
  let H : AffineSubspace ℂ (Point d) := affineSpan ℂ T
  have hTsub : T ⊆ Z.points := by
    rintro y ⟨x, hxG, rfl⟩
    rw [hF]
    exact (hGmem x).mp hxG
  have hTsubF : T ⊆ (F : Set (Point d)) := by
    rintro y ⟨x, hxG, rfl⟩
    exact (hGmem x).mp hxG
  have hHle : H ≤ F := affineSpan_le_of_subset_coe hTsubF
  have hHne : H ≠ F := by
    intro hHF
    have hclosure : AffineVariety.closure T = Z := by
      apply AffineVariety.ext
      apply le_antisymm
      · intro f hf
        change f ∈ MvPolynomial.vanishingIdeal ℂ T at hf
        change f ∈ Z.ideal
        rw [← AffineVariety.vanishingIdeal_points Z]
        rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
        intro z hz
        have hfvan : ∀ x ∈ G, MvPolynomial.eval (toC x) f = 0 := by
          intro x hx
          exact hf (toC x) (Set.mem_image_of_mem toC hx)
        have hzF : z ∈ F := by
          change z ∈ Z.points at hz
          rw [hF] at hz
          exact hz
        have hzH : z ∈ H := by rw [hHF]; exact hzF
        exact dnonreal_vanishing_on_affineSpan G x₀ hx₀G f hfvan z hzH
      · intro f hf
        change f ∈ Z.ideal at hf
        rw [← AffineVariety.vanishingIdeal_points Z] at hf
        change f ∈ MvPolynomial.vanishingIdeal ℂ T
        rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
        intro z hz
        rcases hz with ⟨x, hxG, rfl⟩
        exact hf (toC x) (hTsub (Set.mem_image_of_mem toC hxG))
    have hreal : IsRealFlat Z := by
      refine ⟨G, ⟨x₀, hx₀G⟩, ?_⟩
      change Z.points = (AffineVariety.closure T).points
      rw [hclosure]
    exact hnonreal hreal
  have hHlt : H < F := lt_of_le_of_ne hHle hHne
  obtain ⟨z, hzF, hznotH⟩ := AffineSubspace.exists_of_lt hHlt
  have hx₀H : toC x₀ ∈ H := subset_affineSpan ℂ T
    (Set.mem_image_of_mem toC hx₀G)
  have hvnot : z -ᵥ toC x₀ ∉ H.direction := by
    intro hv
    have hzH : (z -ᵥ toC x₀) +ᵥ toC x₀ ∈ H :=
      AffineSubspace.vadd_mem_of_mem_direction hv hx₀H
    exact hznotH (by simpa using hzH)
  obtain ⟨L, hLv, hker⟩ := Submodule.exists_le_ker_of_notMem hvnot
  let f : Poly d := dnonrealAffineLinearPoly L (toC x₀)
  refine ⟨f, ?_, ?_, ?_⟩
  · exact dnonrealAffineLinearPoly_degree L (toC x₀)
  · intro x hxZ
    have hxF : toC x ∈ F := by
      change toC x ∈ Z.points at hxZ
      rw [hF] at hxZ
      exact hxZ
    have hxG : x ∈ G := (hGmem x).2 hxF
    have hxH : toC x ∈ H := subset_affineSpan ℂ T
      (Set.mem_image_of_mem toC hxG)
    rw [dnonrealAffineLinearPoly_eval]
    apply hker
    exact AffineSubspace.vsub_mem_direction hxH hx₀H
  · refine ⟨z, ?_, ?_⟩
    · change z ∈ Z.points
      rw [hF]
      exact hzF
    · rw [dnonrealAffineLinearPoly_eval]
      exact hLv

/-! ### Product testing (`profiles.tex:438–511`) -/

/-- An assignment of every pool point to one carrier (after `j` cuts) of its own piece that
contains it (`profiles.tex:448–451`). -/
def CarrierAssignment (pl : Finset (Piece d)) (j : ℕ) (α : Pt d → AffineVariety d) : Prop :=
  ∀ X ∈ pl, ∀ p ∈ X.pts, X.path.IsCarrier j (α p) ∧ toC p ∈ α p

/-- Specialize the source variables of a polynomial on pairs. -/
private def dprofiles2PairSourceSlice (F : PairPoly d) (x : Point d) : Poly d :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin d ⊕ Fin d => match i with
      | Sum.inl k => MvPolynomial.C (x k)
      | Sum.inr k => MvPolynomial.X k) F

/-- Specialize the target variables of a polynomial on pairs. -/
private def dprofiles2PairTargetSlice (F : PairPoly d) (y : Point d) : Poly d :=
  dprofiles2PairSourceSlice (MvPolynomial.rename Sum.swap F) y

private theorem dprofiles2PairSourceSlice_degree (F : PairPoly d) (x : Point d) :
    (dprofiles2PairSourceSlice F x).totalDegree ≤ F.totalDegree := by
  classical
  change (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : Fin d ⊕ Fin d => match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) F).totalDegree ≤ F.totalDegree
  conv_lhs => rw [MvPolynomial.as_sum F]
  simp only [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [MvPolynomial.eval₂Hom_monomial]
  have hfactor (i : Fin d ⊕ Fin d) (e : ℕ) :
      ((match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) ^ e).totalDegree ≤
        (match i with | Sum.inl _ => 0 | Sum.inr _ => e) := by
    cases i with
    | inl k =>
      calc
        _ ≤ e * (MvPolynomial.C (x k) : Poly d).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ = 0 := by simp
    | inr k => simpa using (MvPolynomial.totalDegree_pow (MvPolynomial.X k) e)
  have hprod :
      (m.prod fun i e => (match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) ^ e).totalDegree ≤
      m.sum fun i e => (match i with | Sum.inl _ => 0 | Sum.inr _ => e) := by
    have hprodDegree :
        (m.support.prod fun i => (match i with
          | Sum.inl k => MvPolynomial.C (x k)
          | Sum.inr k => MvPolynomial.X k) ^ m i).totalDegree ≤
          ∑ i ∈ m.support, ((match i with
            | Sum.inl k => MvPolynomial.C (x k)
            | Sum.inr k => MvPolynomial.X k) ^ m i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    have hterms :
        (∑ i ∈ m.support, ((match i with
            | Sum.inl k => MvPolynomial.C (x k)
            | Sum.inr k => MvPolynomial.X k) ^ m i).totalDegree) ≤
          ∑ i ∈ m.support, (match i with | Sum.inl _ => 0 | Sum.inr _ => m i) :=
      Finset.sum_le_sum (fun i hi => hfactor i (m i))
    rw [Finsupp.prod, Finsupp.sum]
    exact hprodDegree.trans hterms
  have hle :
      (m.sum fun i e => (match i with | Sum.inl _ => 0 | Sum.inr _ => e)) ≤
        m.sum fun _ e => e := by
    apply Finsupp.sum_le_sum
    intro i e
    cases i <;> simp
  calc
    _ ≤ (MvPolynomial.C (F.coeff m)).totalDegree +
        (m.prod fun i e => (match i with
          | Sum.inl k => MvPolynomial.C (x k)
          | Sum.inr k => MvPolynomial.X k) ^ e).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ m.sum fun _ e => e := by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact hprod.trans hle
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hm

private theorem dprofiles2PairTargetSlice_degree (F : PairPoly d) (y : Point d) :
    (dprofiles2PairTargetSlice F y).totalDegree ≤ F.totalDegree := by
  classical
  have h := dprofiles2PairSourceSlice_degree (d := d) (MvPolynomial.rename Sum.swap F) y
  have h1 := MvPolynomial.totalDegree_rename_le Sum.swap F
  simpa [dprofiles2PairTargetSlice] using h.trans h1

private theorem dprofiles2PairSourceSlice_eval (F : PairPoly d) (x y : Point d) :
    MvPolynomial.eval y (dprofiles2PairSourceSlice F x) =
      MvPolynomial.eval (pairPt x y) F := by
  classical
  change MvPolynomial.eval y (MvPolynomial.eval₂ MvPolynomial.C
      (fun i : Fin d ⊕ Fin d => match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) F) = _
  rw [MvPolynomial.eval_eval₂]
  have hcoeff : (MvPolynomial.eval y).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hcoeff, MvPolynomial.eval₂_id]
  have hvars : (fun i : Fin d ⊕ Fin d => MvPolynomial.eval y
      (match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k)) = pairPt x y := by
    funext i
    cases i <;> simp [pairPt]
  simp [hvars]

private theorem dprofiles2PairTargetSlice_eval (F : PairPoly d) (x y : Point d) :
    MvPolynomial.eval x (dprofiles2PairTargetSlice F y) =
      MvPolynomial.eval (pairPt x y) F := by
  classical
  change MvPolynomial.eval x (dprofiles2PairSourceSlice (MvPolynomial.rename Sum.swap F) y) = _
  rw [dprofiles2PairSourceSlice_eval]
  rw [MvPolynomial.eval_rename]
  have hp : pairPt y x ∘ Sum.swap = pairPt x y := by
    funext i
    cases i <;> rfl
  rw [hp]

private theorem dprofiles2_close_plateau {d : ℕ} (t u : Fin d → ℝ) (j : ℕ)
    (η b ρ : ℝ) (hclose : ∀ i, |u i - t i| ≤ ρ) (hρ : ρ ≤ η / 2)
    (hplateau : OnPlateau t j (2 * η) b) : OnPlateau u j η b := by
  intro i
  have hdiff := abs_le.mp (hclose i)
  constructor
  · intro hi
    have ht := (hplateau i).1 hi
    nlinarith
  · intro hi
    have ht := (hplateau i).2 hi
    nlinarith

private theorem dprofiles2_cardPairsBoundFst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (B : Finset (α × β))
    (hB : B ⊆ S ×ˢ T) (u : ℝ)
    (hfiber : ∀ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) ≤
      u * (T.card : ℝ)) :
    (B.card : ℝ) ≤ u * (S.card : ℝ) * (T.card : ℝ) := by
  classical
  have hmaps : (B : Set (α × β)).MapsTo Prod.fst S := by
    intro z hz
    exact (Finset.mem_product.mp (hB hz)).1
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiberCard (x : α) :
      (B.filter (fun z => z.1 = x)).card = (T.filter (fun y => (x, y) ∈ B)).card := by
    apply Finset.card_bij (fun z hz => z.2)
    · intro z hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzx := (Finset.mem_filter.mp hz).2
      have hzT := (Finset.mem_product.mp (hB hzB)).2
      have hzEq : z = (x, z.2) := Prod.ext hzx rfl
      have hzB' : (x, z.2) ∈ B := hzEq ▸ hzB
      exact Finset.mem_filter.mpr ⟨hzT, hzB'⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      apply Prod.ext
      · exact (Finset.mem_filter.mp hz₁).2.trans (Finset.mem_filter.mp hz₂).2.symm
      · exact heq
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyT, hyB⟩
      exact ⟨(x, y), Finset.mem_filter.mpr ⟨hyB, rfl⟩, rfl⟩
  have hsumReal : (B.card : ℝ) =
      ∑ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) := by
    calc
      (B.card : ℝ) = ((∑ x ∈ S, (B.filter (fun z => z.1 = x)).card : ℕ) : ℝ) := by
        rw [hsum]
      _ = ∑ x ∈ S, ((B.filter (fun z => z.1 = x)).card : ℝ) := by norm_cast
      _ = ∑ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact_mod_cast hfiberCard x
  calc
    (B.card : ℝ) = ∑ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) := hsumReal
    _ ≤ ∑ x ∈ S, u * (T.card : ℝ) := Finset.sum_le_sum (by
      intro x hx
      exact hfiber x hx)
    _ = u * (S.card : ℝ) * (T.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_cast
      ring

private theorem dprofiles2_cardPairsBoundSnd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (B : Finset (α × β))
    (hB : B ⊆ S ×ˢ T) (u : ℝ)
    (hfiber : ∀ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) ≤
      u * (S.card : ℝ)) :
    (B.card : ℝ) ≤ u * (T.card : ℝ) * (S.card : ℝ) := by
  classical
  have hmaps : (B : Set (α × β)).MapsTo Prod.snd T := by
    intro z hz
    exact (Finset.mem_product.mp (hB hz)).2
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiberCard (y : β) :
      (B.filter (fun z => z.2 = y)).card = (S.filter (fun x => (x, y) ∈ B)).card := by
    apply Finset.card_bij (fun z hz => z.1)
    · intro z hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzy := (Finset.mem_filter.mp hz).2
      have hzS := (Finset.mem_product.mp (hB hzB)).1
      have hzEq : z = (z.1, y) := Prod.ext rfl hzy
      have hzB' : (z.1, y) ∈ B := hzEq ▸ hzB
      exact Finset.mem_filter.mpr ⟨hzS, hzB'⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      apply Prod.ext
      · exact heq
      · exact (Finset.mem_filter.mp hz₁).2.trans (Finset.mem_filter.mp hz₂).2.symm
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxS, hxB⟩
      exact ⟨(x, y), Finset.mem_filter.mpr ⟨hxB, rfl⟩, rfl⟩
  have hsumReal : (B.card : ℝ) =
      ∑ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) := by
    calc
      (B.card : ℝ) = ((∑ y ∈ T, (B.filter (fun z => z.2 = y)).card : ℕ) : ℝ) := by
        rw [hsum]
      _ = ∑ y ∈ T, ((B.filter (fun z => z.2 = y)).card : ℝ) := by norm_cast
      _ = ∑ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact_mod_cast hfiberCard y
  calc
    (B.card : ℝ) = ∑ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) := hsumReal
    _ ≤ ∑ y ∈ T, u * (S.card : ℝ) := Finset.sum_le_sum (by
      intro y hy
      exact hfiber y hy)
    _ = u * (T.card : ℝ) * (S.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_cast
      ring

/-- The label `ψ(x, y) = (x, π_x y)` in the direction chart `u_{i₀} = 1`:
`(x, (y - x) / (y - x)_{i₀})`, as a point of the pair space. -/
def labelPt (i₀ : Fin d) (x y : Point d) : Fin d ⊕ Fin d → ℂ :=
  pairPt x (((y - x) i₀)⁻¹ • (y - x))

/-- The homogeneous numerator of one monomial after pulling back the direction chart. -/
private def dprofiles2LabelClearTerm (i₀ : Fin d) (N : ℕ)
    (m : (Fin d ⊕ Fin d) →₀ ℕ) (c : ℂ) : PairPoly d :=
  MvPolynomial.C c *
    (m.prod fun i e => match i with
      | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
      | Sum.inr k =>
          (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e) *
    (MvPolynomial.X (Sum.inr i₀) - MvPolynomial.X (Sum.inl i₀)) ^
      (N - m.sum fun i e => match i with
        | Sum.inl _ => 0
        | Sum.inr _ => e)

/-- Clear a common denominator of exponent `N` in the chart pullback. -/
private def dprofiles2LabelClear (i₀ : Fin d) (N : ℕ) (G : PairPoly d) : PairPoly d :=
  ∑ m ∈ G.support, dprofiles2LabelClearTerm i₀ N m (G.coeff m)

private theorem dprofiles2LabelClearTerm_degree (i₀ : Fin d) (N : ℕ)
    (m : (Fin d ⊕ Fin d) →₀ ℕ) (c : ℂ)
    (htotal : m.sum (fun _ e => e) ≤ N) :
    (dprofiles2LabelClearTerm i₀ N m c).totalDegree ≤ 2 * N := by
  classical
  let δ : PairPoly d := MvPolynomial.X (Sum.inr i₀) - MvPolynomial.X (Sum.inl i₀)
  let base : PairPoly d := m.prod fun i e => match i with
    | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
    | Sum.inr k => (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e
  have hfactorL (k : Fin d) (e : ℕ) :
      ((MvPolynomial.X (Sum.inl k) : PairPoly d) ^ e).totalDegree ≤ e := by simp
  have hfactorR (k : Fin d) (e : ℕ) :
      (((MvPolynomial.X (Sum.inr k) : PairPoly d) - MvPolynomial.X (Sum.inl k)) ^ e).totalDegree ≤ e := by
    have hbase :
        ((MvPolynomial.X (Sum.inr k) : PairPoly d) - MvPolynomial.X (Sum.inl k)).totalDegree ≤ 1 := by
      calc
        _ ≤ max (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inr k) : PairPoly d))
            (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inl k) : PairPoly d)) :=
          MvPolynomial.totalDegree_sub _ _
        _ ≤ 1 := by simp
    calc
      _ ≤ e * ((MvPolynomial.X (Sum.inr k) : PairPoly d) -
          MvPolynomial.X (Sum.inl k)).totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ e * 1 := Nat.mul_le_mul_left _ hbase
      _ = e := Nat.mul_one _
  have hbase : base.totalDegree ≤ m.sum (fun _ e => e) := by
    change ((∏ i ∈ m.support, (match i with
      | Sum.inl k => (MvPolynomial.X (Sum.inl k) : PairPoly d) ^ m i
      | Sum.inr k => ((MvPolynomial.X (Sum.inr k) : PairPoly d) -
          MvPolynomial.X (Sum.inl k)) ^ m i)).totalDegree) ≤ _
    calc
      _ ≤ ∑ i ∈ m.support,
          ((match i with
            | Sum.inl k => (MvPolynomial.X (Sum.inl k) : PairPoly d) ^ m i
            | Sum.inr k =>
                ((MvPolynomial.X (Sum.inr k) : PairPoly d) -
                  MvPolynomial.X (Sum.inl k)) ^ m i) : PairPoly d).totalDegree :=
        MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ m.support, m i := Finset.sum_le_sum (by
        intro i hi
        cases i with
        | inl k => simpa using hfactorL k (m (Sum.inl k))
        | inr k => simpa using hfactorR k (m (Sum.inr k)))
      _ = m.sum (fun _ e => e) := by rw [Finsupp.sum]
  have hδ : δ.totalDegree ≤ 1 := by
    dsimp [δ]
    calc
      _ ≤ max (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inr i₀) : PairPoly d))
          (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inl i₀) : PairPoly d)) :=
        MvPolynomial.totalDegree_sub _ _
      _ ≤ 1 := by simp
  have hδpow (q : ℕ) : (δ ^ q).totalDegree ≤ q := by
    calc
      _ ≤ q * δ.totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ q * 1 := Nat.mul_le_mul_left _ hδ
      _ = q := Nat.mul_one _
  have hq : N - m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e) ≤ N := Nat.sub_le _ _
  change (MvPolynomial.C c * base * δ ^ (N - m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e))).totalDegree ≤ 2 * N
  calc
    _ ≤ (MvPolynomial.C c).totalDegree + base.totalDegree +
        (δ ^ (N - m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e))).totalDegree := by
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _)
    _ ≤ 0 + N + (N - m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e)) := by
      exact Nat.add_le_add (Nat.add_le_add (by simp) (hbase.trans htotal))
        (hδpow _)
    _ ≤ 2 * N := by omega

private theorem dprofiles2LabelClear_degree (i₀ : Fin d) (N : ℕ) (G : PairPoly d)
    (hG : G.totalDegree ≤ N) : (dprofiles2LabelClear i₀ N G).totalDegree ≤ 2 * N := by
  classical
  unfold dprofiles2LabelClear
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply dprofiles2LabelClearTerm_degree
  exact (MvPolynomial.le_totalDegree hm).trans hG

private theorem dprofiles2LabelClearTerm_eval (i₀ : Fin d) (N : ℕ)
    (m : (Fin d ⊕ Fin d) →₀ ℕ) (c : ℂ) (x y : Point d)
    (htotal : m.sum (fun _ e => e) ≤ N)
    (hδ : (y - x) i₀ ≠ 0) :
    MvPolynomial.eval (pairPt x y) (dprofiles2LabelClearTerm i₀ N m c) =
      ((y - x) i₀) ^ N *
        MvPolynomial.eval (labelPt i₀ x y) (MvPolynomial.monomial m c) := by
  classical
  let u : Point d := y - x
  let δ : ℂ := u i₀
  let base : PairPoly d := m.prod fun i e => match i with
    | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
    | Sum.inr k => (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e
  have hδ' : δ ≠ 0 := by simpa [δ, u] using hδ
  have hsecond : m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e) ≤ N := by
    calc
      _ ≤ m.sum (fun _ e => e) := by
        apply Finsupp.sum_le_sum
        intro i e
        cases i <;> simp
      _ ≤ N := htotal
  let labelCoord : Fin d ⊕ Fin d → ℂ := fun i => match i with
    | Sum.inl k => x k
    | Sum.inr k => δ⁻¹ * u k
  have hlabel (i : Fin d ⊕ Fin d) : labelPt i₀ x y i = labelCoord i := by
    cases i with
    | inl k => simp [labelPt, labelCoord, pairPt]
    | inr k => simp [labelPt, labelCoord, pairPt, u, δ, smul_eq_mul]
  have hfactor (i : Fin d ⊕ Fin d) (e : ℕ) :
      (match i with
        | Sum.inl k => x k ^ e
        | Sum.inr k => u k ^ e) =
      labelCoord i ^ e * δ ^ (match i with
        | Sum.inl _ => 0
        | Sum.inr _ => e) := by
    cases i with
    | inl k => change x k ^ e = x k ^ e * δ ^ 0; simp
    | inr k =>
      change u k ^ e = (δ⁻¹ * u k) ^ e * δ ^ e
      have hmul : (δ⁻¹ * u k) * δ = u k := by
        calc
          _ = δ⁻¹ * (u k * δ) := by ring
          _ = δ⁻¹ * (δ * u k) := by rw [mul_comm (u k) δ]
          _ = (δ⁻¹ * δ) * u k := by ring
          _ = u k := by simp [hδ']
      calc
        u k ^ e = ((δ⁻¹ * u k) * δ) ^ e := by rw [hmul]
        _ = (δ⁻¹ * u k) ^ e * δ ^ e := by rw [mul_pow]
  have hbaseEval : MvPolynomial.eval (pairPt x y) base =
      m.prod (fun i e => match i with
        | Sum.inl k => x k ^ e
        | Sum.inr k => u k ^ e) := by
    change MvPolynomial.eval (pairPt x y) (m.prod fun i e => match i with
      | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
      | Sum.inr k => (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e) = _
    rw [Finsupp.prod, Finsupp.prod, MvPolynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i hi
    cases i <;> simp [pairPt, u]
  have hprod :
      m.prod (fun i e => match i with
        | Sum.inl k => x k ^ e
        | Sum.inr k => u k ^ e) =
      (m.prod fun i e => labelCoord i ^ e) *
        δ ^ m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e) := by
    calc
      _ = m.prod (fun i e => labelCoord i ^ e *
          δ ^ (match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e)) := by
        exact Finsupp.prod_congr (fun i hi => hfactor i (m i))
      _ = (m.prod fun i e => labelCoord i ^ e) *
          (m.prod fun i e => δ ^ (match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e)) := Finsupp.prod_mul
      _ = (m.prod fun i e => labelCoord i ^ e) *
          δ ^ m.sum (fun i e => match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e) := by
        congr 1
        rw [Finsupp.prod, Finsupp.sum]
        exact Finset.prod_pow_eq_pow_sum m.support
          (fun i => match i with
            | Sum.inl _ => 0
            | Sum.inr _ => m i) δ
  have hpow : δ ^ m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e) *
      δ ^ (N - m.sum (fun i e => match i with
        | Sum.inl _ => 0
        | Sum.inr _ => e)) = δ ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hsecond]
  have hlabelProd : MvPolynomial.eval (labelPt i₀ x y)
      (MvPolynomial.monomial m c) = c * (m.prod fun i e => labelCoord i ^ e) := by
    rw [MvPolynomial.eval_monomial]
    congr 1
    exact Finsupp.prod_congr (fun i hi => by rw [hlabel i])
  have hδeval : MvPolynomial.eval (pairPt x y)
      (MvPolynomial.X (Sum.inr i₀) - MvPolynomial.X (Sum.inl i₀)) = δ := by
    simp [pairPt, u, δ]
  rw [dprofiles2LabelClearTerm, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, hbaseEval, MvPolynomial.eval_pow, hδeval,
    hlabelProd, hprod]
  calc
    c * ((m.prod fun i e => labelCoord i ^ e) *
        δ ^ m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e)) *
        δ ^ (N - m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e)) =
      (c * (m.prod fun i e => labelCoord i ^ e)) *
        (δ ^ m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e) *
          δ ^ (N - m.sum (fun i e => match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e))) := by ring
    _ = _ := by rw [hpow]
    _ = _ := by
      rw [mul_comm (c * (m.prod fun i e => labelCoord i ^ e)) (δ ^ N)]

private theorem dprofiles2LabelClear_eval (i₀ : Fin d) (N : ℕ) (G : PairPoly d)
    (hG : G.totalDegree ≤ N) (x y : Point d) (hδ : (y - x) i₀ ≠ 0) :
    MvPolynomial.eval (pairPt x y) (dprofiles2LabelClear i₀ N G) =
      ((y - x) i₀) ^ N * MvPolynomial.eval (labelPt i₀ x y) G := by
  classical
  rw [dprofiles2LabelClear, MvPolynomial.eval_sum]
  calc
    _ = ∑ m ∈ G.support,
        ((y - x) i₀) ^ N *
          MvPolynomial.eval (labelPt i₀ x y) (MvPolynomial.monomial m (G.coeff m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact dprofiles2LabelClearTerm_eval i₀ N m (G.coeff m) x y
        ((MvPolynomial.le_totalDegree hm).trans hG) hδ
    _ = ((y - x) i₀) ^ N *
        MvPolynomial.eval (labelPt i₀ x y)
          (∑ m ∈ G.support, MvPolynomial.monomial m (G.coeff m)) := by
      rw [MvPolynomial.eval_sum, Finset.mul_sum]
    _ = _ := by rw [← G.as_sum]

/-- Choose one finite linear combination that stays nonzero at each of finitely many witnesses. -/
private theorem dprofiles2_exists_generic_coefficients {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ι → ℂ) (hdiag : ∀ i ∈ s, v i i ≠ 0) :
    ∃ c : ι → ℂ, ∀ i ∈ s, (∑ j ∈ s, c j * v j i) ≠ 0 := by
  classical
  revert hdiag
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      intro hdiag
      have hdiagS : ∀ i ∈ s, v i i ≠ 0 := fun i hi => hdiag i (Finset.mem_insert_of_mem hi)
      obtain ⟨c, hc⟩ := ih hdiagS
      let oldSum : ι → ℂ := fun i => ∑ j ∈ s, c j * v j i
      let forbidden : Finset ℂ :=
        (s.image fun i => if hv : v a i = 0 then 0 else -oldSum i / v a i) ∪
          {-oldSum a / v a a}
      obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset forbidden
      let c' : ι → ℂ := Function.update c a t
      have hsum (i : ι) :
          (∑ j ∈ insert a s, c' j * v j i) = oldSum i + t * v a i := by
        rw [Finset.sum_insert ha]
        have htail : (∑ j ∈ s, c' j * v j i) = oldSum i := by
          apply Finset.sum_congr rfl
          intro j hj
          have hja : j ≠ a := fun h => ha (h ▸ hj)
          simp [c', oldSum, hja]
        calc
          _ = t * v a i + oldSum i := by
            rw [show c' a = t by simp [c'], htail]
          _ = oldSum i + t * v a i := by ring
      have hnew (i : ι) (hi : i ∈ s) : oldSum i + t * v a i ≠ 0 := by
        by_cases hv : v a i = 0
        · simpa [oldSum, hv] using hc i hi
        · intro hz
          have htval : t = -oldSum i / v a i := by
            calc
              t = (t * v a i) / v a i := by field_simp [hv]
              _ = -oldSum i / v a i := by
                congr 1
                linear_combination hz
          have hmem : t ∈ s.image
              (fun q => if hq : v a q = 0 then 0 else -oldSum q / v a q) := by
            apply Finset.mem_image.mpr
            refine ⟨i, hi, ?_⟩
            simpa [hv] using htval.symm
          exact ht (Finset.mem_union.mpr (Or.inl hmem))
      have hnewA : oldSum a + t * v a a ≠ 0 := by
        have hdiagA := hdiag a (Finset.mem_insert_self a s)
        intro hz
        have htval : t = -oldSum a / v a a := by
          calc
            t = (t * v a a) / v a a := by field_simp [hdiagA]
            _ = -oldSum a / v a a := by
              congr 1
              linear_combination hz
        have hmem : t ∈ ({-oldSum a / v a a} : Finset ℂ) := by simp [htval]
        exact ht (Finset.mem_union.mpr (Or.inr hmem))
      refine ⟨c', ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa [hsum] using hnewA
      · rw [hsum]
        exact hnew i hi

end

end TrackD
end DistinctDistances
