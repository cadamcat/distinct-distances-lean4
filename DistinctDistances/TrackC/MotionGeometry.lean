import DistinctDistances.TrackC.Planar
import DistinctDistances.TrackC.FiniteSpatialRotation

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/- Keep this original definition prefix in order: its generated numeral proof
names are part of the frozen structural hashes. -/

def spannedLines {d : ℕ} (X : Finset (E d)) : Set (Line d) := richLines X 2

def anchors {d : ℕ} (X : Finset (E d)) (γ : ℝ) : Finset (E d) :=
  X.filter (fun x => γ * X.card ≤
    ({l : Line d | l ∈ spannedLines X ∧ x ∈ l.1}.ncard : ℝ))

def richestLineOccupancy (X : Finset (E 3)) (H : Plane 3) : ℕ :=
  sSup {n : ℕ | ∃ l : Line 3, l.1 ≤ H.1 ∧ (pointsOn X l).card = n}

def effectiveSize (X : Finset (E 3)) (H : Plane 3) : ℕ :=
  (pointsOn X H).card - richestLineOccupancy X H

def planePairEnergy (X : Finset (E 3)) (P : Finset (Plane 3)) : ℕ :=
  ∑ HH' ∈ P.offDiag, (X.filter (fun x => x ∈ HH'.1.1 ∧ x ∈ HH'.2.1)).card

def nonLineType (η ℓ : ℝ) (X Y : Finset (E 3)) (g : Motion 3) : Prop :=
  ∀ l : Line 3, ((pointsOn (matchPoints X Y g) l).card : ℝ) < η * ℓ

def planarType (η ℓ : ℝ) (X Y : Finset (E 3)) (g : Motion 3) : Prop :=
  ∃ H : Plane 3, η * ℓ ≤ ((pointsOn (matchPoints X Y g) H).card : ℝ)

def motionBucket (X Y : Finset (E 3)) (ℓ : ℝ) : Set (Motion 3) :=
  {g | ℓ ≤ (matchCount X Y g : ℝ) ∧ (matchCount X Y g : ℝ) < 2 * ℓ}

def reverseMotion (g : Motion 3) : Prop :=
  LinearMap.det g.toAffineEquiv.linear.toLinearMap = -1

def axis (g : Motion 3) : Submodule ℝ (E 3) :=
  LinearMap.ker (g.toAffineEquiv.linear.toLinearMap + LinearMap.id)

def axisAvoidsTriples (g : Motion 3) (S : Finset (E 3)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ¬ Collinear ℝ ({x, y, z} : Set (E 3)) →
    axis g ⊓ vectorSpan ℝ ({x, y, z} : Set (E 3)) = ⊥

def wCoord (z : E 6) : E 3 := WithLp.toLp 2 (fun i => z (i.castAdd 3))
def cCoord (z : E 6) : E 3 := WithLp.toLp 2 (fun i => z (i.natAdd 3))
def cross3 (u v : E 3) : E 3 := WithLp.toLp 2
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

def splitQuadratic (z : E 6) : ℝ := ∑ i : Fin 3, wCoord z i * cCoord z i
def maximalNull (H : Flat 6 3) : Prop := ∀ z ∈ H.1.direction, splitQuadratic z = 0
def pairFlatSet (x y : E 3) : Set (E 6) :=
  {z | (1 / 2 : ℝ) • (x - y) = cross3 (wCoord z) ((1 / 2 : ℝ) • (x + y)) + cCoord z}

def graphDualPlane (x : E 3) : Set (E 3) :=
  {u | u 2 + u 0 * x 0 + u 1 * x 1 = x 2}

/-- The concrete null-flat and graph-duality data used by derivative propagation. -/
def MotionFlatModel (g : Motion 3) (S : Finset (E 3)) (G : Flat 6 3) : Prop :=
  maximalNull G ∧
    ∃ (T : E 3 ≃ᵃ[ℝ] E 3) (φ : E 3 →ᵃ[ℝ] E 6),
      Function.Injective φ ∧ Set.range φ = (G.1 : Set (E 6)) ∧
      (∀ x ∈ S, pairFlatSet x (g x) ∩ (G.1 : Set (E 6)) = φ '' graphDualPlane (T x)) ∧
      (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
        ¬ Collinear ℝ ({x, y, z} : Set (E 3)) →
          ¬ Collinear ℝ
            ({WithLp.toLp 2 ![T x 0, T x 1], WithLp.toLp 2 ![T y 0, T y 1],
              WithLp.toLp 2 ![T z 0, T z 1]} : Set (E 2)))

def raisedGradient (f : Poly 6) (z : E 6) : E 6 :=
  WithLp.toLp 2 (Fin.addCases (motive := fun _ : Fin 6 => ℝ)
    (fun i : Fin 3 => evalR (MvPolynomial.pderiv (i.natAdd 3) f) z)
    (fun i : Fin 3 => evalR (MvPolynomial.pderiv (i.castAdd 3) f) z))

end DistinctDistances.TrackC
