import DistinctDistances.TrackD.Terminal

/-!
# Pieces, cut paths and profiles (`profiles.tex:15–47, 228–233`)

A piece is a set of sample points with one path of `d` polynomial cuts and recorded normalized
cut times. Finitary conventions (see `TrackD/Basic.lean`): the paper's limiting cut times
`b_1 ≤ … ≤ b_d` are replaced by the recorded times `t_i` of the piece, and an "open plateau"
by the set of `b` at distance at least a margin `ξ` from every recorded time (`OnPlateau`).
Errors `exp(±o(s))` are explicit factors `exp(±θ s)`.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

variable {d : ℕ}

/-- Testing degree `T_s(b) = B e^{b s}` (`profiles.tex:18`). -/
def testDeg (B s b : ℝ) : ℝ := B * Real.exp (b * s)

/-- A path of `d` polynomial cuts `f_1, …, f_d` (indexed by `Fin d`) with recorded normalized
cut times `t_i` (`profiles.tex:40–43`). -/
structure CutPath (d : ℕ) where
  cut : Fin d → Poly d
  time : Fin d → ℝ

namespace CutPath

/-- The ideal of the system after the first `j` cuts. -/
def system (π : CutPath d) (j : ℕ) : Ideal (Poly d) :=
  Ideal.span {f | ∃ i : Fin d, i.val < j ∧ π.cut i = f}

/-- `Z` is an irreducible component of the system after `j` cuts. -/
def IsCarrier (π : CutPath d) (j : ℕ) (Z : AffineVariety d) : Prop :=
  Z.IsComponentOf (π.system j)

/-- Local carriers at `x` after `j` cuts: the components of the `j`-cut system through `x`
(`profiles.tex:34–37`). -/
def localCarriers (π : CutPath d) (j : ℕ) (x : Point d) : Set (AffineVariety d) :=
  {Z | π.IsCarrier j Z ∧ x ∈ Z}

/-- Properness at `x`: every cut is nonzero on every component of the preceding system through
`x` (`profiles.tex:33–34`). -/
def ProperAt (π : CutPath d) (x : Point d) : Prop :=
  ∀ i : Fin d, ∀ Z ∈ π.localCarriers i.val x, π.cut i ∉ Z.ideal

/-- Points of `S` captured by `g` after `j` cuts: `g` vanishes there but contains none of the
local carriers (`profiles.tex:68–70`). -/
def captured (π : CutPath d) (j : ℕ) (S : Finset (Pt d)) (g : Poly d) : Finset (Pt d) :=
  S.filter (fun x => MvPolynomial.eval (toC x) g = 0 ∧
    ∀ Z ∈ π.localCarriers j (toC x), g ∉ Z.ideal)

end CutPath

/-- `b` lies on the plateau after exactly `j` cuts, at distance at least `ξ` from every recorded
cut time (the finitary form of "strictly between consecutive distinct limiting cut times"). -/
def OnPlateau (t : Fin d → ℝ) (j : ℕ) (ξ b : ℝ) : Prop :=
  ∀ i : Fin d, (i.val < j → t i + ξ ≤ b) ∧ (j ≤ i.val → b + ξ ≤ t i)

/-- `D_i = B e^{t_i s}`. -/
def cutScale (B s : ℝ) (t : Fin d → ℝ) (i : Fin d) : ℝ := testDeg B s (t i)

/-- `e_j = ∏_{i ≤ j} D_i` (paper indices; here the first `j` cuts). -/
def eScale (B s : ℝ) (t : Fin d → ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), cutScale B s t i

/-- `∏_{i > j} D_i` (paper indices; here the cuts after the first `j`). -/
def tailScale (B s : ℝ) (t : Fin d → ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val), cutScale B s t i

/-- The profile function `σ(b) = ∏_i min(T_s(b), D_i)` (`profiles.tex:230–233`). -/
def sigma (B s : ℝ) (t : Fin d → ℝ) (b : ℝ) : ℝ :=
  ∏ i, min (testDeg B s b) (cutScale B s t i)

/-- A piece: sample points, a dyadic width and one path of cuts (`profiles.tex:31–33`). -/
structure Piece (d : ℕ) where
  pts : Finset (Pt d)
  width : ℝ
  path : CutPath d

/-- The properties of a non-core piece in `prof:partition` (`profiles.tex:55–75`), with
tolerance `θ` for every `o(·)`, plateau margin `ξ`, and degree constant `K` in the no-capture
property ("uniformly over polynomials of degree `O(T_s(b))`"). -/
structure PieceGood (P : Finset (Pt d)) (θ ξ K : ℝ) (X : Piece d) : Prop where
  subset : X.pts ⊆ P
  width_dyadic : ∃ a : ℕ, X.width = Real.log (cfgB P) / 2 ^ a
  size : cfgN P * Real.exp (-θ * X.width) ≤ X.pts.card
  mono : Monotone X.path.time
  time_range : ∀ i, -1 ≤ X.path.time i ∧ X.path.time i ≤ 1 + θ
  imbalance : ∃ i, 1 / 2 - θ ≤ |X.path.time i|
  vanish : ∀ x ∈ X.pts, ∀ i, MvPolynomial.eval (toC x) (X.path.cut i) = 0
  proper : ∀ x ∈ X.pts, X.path.ProperAt (toC x)
  degree : ∀ i, ((X.path.cut i).totalDegree : ℝ) ≤
    testDeg (cfgB P) X.width (X.path.time i + θ)
  noCapture : ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
    1 ≤ testDeg (cfgB P) X.width b →
    ∀ g : Poly d, (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) X.width b →
      ((X.path.captured j X.pts g).card : ℝ) ≤ θ * X.pts.card

/-- The core is simultaneously isolated by equations of degree `L`: every core point is an
isolated point (a zero-dimensional component) of their common zero set (`profiles.tex:53`). -/
def CoreIsolated (core : Finset (Pt d)) (L : ℕ) : Prop :=
  ∃ F : Set (Poly d), (∀ f ∈ F, f.totalDegree ≤ L) ∧
    ∀ x ∈ core, pointIdeal (toC x) ∈ (Ideal.span F).minimalPrimes

/-- A multiscale partition: core, its isolation degree, and the non-core pieces. -/
structure Partition (d : ℕ) where
  core : Finset (Pt d)
  coreDeg : ℕ
  pieces : Finset (Piece d)

/-- The conclusions of `prof:partition` (`profiles.tex:49–76`) with tolerance `θ`, margin `ξ`,
degree constant `K`, minimal width `s₀`, for the directional degree ratio `δ`
(`E = δ N / A`). -/
structure Partition.Good (Q : Partition d) (P : Finset (Pt d)) (δ θ ξ K s₀ : ℝ) : Prop where
  core_subset : Q.core ⊆ P
  core_isolated : CoreIsolated Q.core Q.coreDeg
  core_degree : δ * cfgN P / cfgA P * (Q.coreDeg : ℝ) ^ 2 ≤ θ * cfgN P
  pieces_good : ∀ X ∈ Q.pieces, PieceGood P θ ξ K X ∧ s₀ ≤ X.width
  pieces_disjoint : (Q.pieces : Set (Piece d)).PairwiseDisjoint Piece.pts
  core_disjoint : ∀ X ∈ Q.pieces, Disjoint Q.core X.pts
  discard : cfgN P - Q.core.card - ∑ X ∈ Q.pieces, (X.pts.card : ℝ) ≤ θ * cfgN P

/-- A pool: pieces of a common width `s` whose recorded times are within `ρ` of a reference
profile `t`, at most `exp(θ s)` of them (`profiles.tex:351–354`, 532–538). A single piece, or two
pieces in a common window with the same profile, are pools. -/
structure PoolGood (P : Finset (Pt d)) (θ ξ K ρ : ℝ) (pl : Finset (Piece d)) (s : ℝ)
    (t : Fin d → ℝ) : Prop where
  pieces : ∀ X ∈ pl, PieceGood P θ ξ K X
  width : ∀ X ∈ pl, X.width = s
  close : ∀ X ∈ pl, ∀ i, |X.path.time i - t i| ≤ ρ
  count : (pl.card : ℝ) ≤ Real.exp (θ * s)
  disjoint : (pl : Set (Piece d)).PairwiseDisjoint Piece.pts

/-- The points of a pool. -/
def poolPts (pl : Finset (Piece d)) : Finset (Pt d) := pl.biUnion Piece.pts

/-- `Z` is a carrier after `j` cuts of some piece of the pool, through one of its points. -/
def PoolCarrier (pl : Finset (Piece d)) (j : ℕ) (Z : AffineVariety d) : Prop :=
  ∃ X ∈ pl, X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z

/-- Kernel of the Jacobian of a finite system at a point. -/
def jacKer (F : Finset (Poly d)) (y : Point d) : Submodule ℂ (Point d) :=
  ⨅ f ∈ F, LinearMap.ker (differential f y)

end

end TrackD
end DistinctDistances
