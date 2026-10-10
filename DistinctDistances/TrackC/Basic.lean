import Mathlib

/-! Concrete coordinate interfaces for track C. These are polynomial and
incidence predicates, not a second model of algebraic varieties. -/

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℝ
/-- Nonempty affine flats; dimension means the rank of the direction space. -/
abbrev Flat (d k : ℕ) :=
  {H : AffineSubspace ℝ (E d) // (H : Set (E d)).Nonempty ∧ Module.finrank ℝ H.direction = k}
abbrev Line (d : ℕ) := Flat d 1
abbrev Plane (d : ℕ) := Flat d 2
/-- Projective points and lines are one- and two-dimensional vector subspaces. -/
abbrev PFlat (K : Type*) [Field K] (n k : ℕ) :=
  {L : Submodule K (Fin n → K) // Module.finrank K L = k}
abbrev Motion (d : ℕ) := AffineIsometryEquiv ℝ (E d) (E d)

def FiniteCardBound {α : Type*} (S : Set α) (b : ℝ) : Prop :=
  S.Finite ∧ (S.ncard : ℝ) ≤ b

noncomputable def pointsOn {d k : ℕ} (X : Finset (E d)) (H : Flat d k) :
    Finset (E d) := by
  classical
  exact X.filter (fun x => x ∈ H.1)

noncomputable def pointsIn {d : ℕ} (X : Finset (E d)) (S : Set (E d)) :
    Finset (E d) := by
  classical
  exact X.filter (fun x => x ∈ S)

noncomputable def lineMultiplicity {d : ℕ} (L : Finset (Line d)) (x : E d) : ℕ := by
  classical
  exact (L.filter (fun l => x ∈ l.1)).card

noncomputable def incidences {d : ℕ} (X : Finset (E d)) (L : Finset (Line d)) : ℕ :=
  ∑ x ∈ X, lineMultiplicity L x

def richPoints {d : ℕ} (L : Finset (Line d)) (k : ℕ) : Set (E d) :=
  {x | k ≤ lineMultiplicity L x}

def richLines {d : ℕ} (X : Finset (E d)) (k : ℝ) : Set (Line d) :=
  {l | k ≤ (pointsOn X l).card}

def planeCap (L : Finset (Line 3)) (B : ℝ) : Prop :=
  ∀ H : Plane 3, ((L.filter (fun l => l.1 ≤ H.1)).card : ℝ) ≤ B

def cloudLineCap {d : ℕ} (X : Finset (E d)) (B : ℝ) : Prop :=
  ∀ l : Line d, ((pointsOn X l).card : ℝ) ≤ B

noncomputable def positiveDistances {d : ℕ} (X : Finset (E d)) : Finset ℝ := by
  classical
  exact X.offDiag.image (fun xy => dist xy.1 xy.2)

noncomputable def matchPoints {d : ℕ} (X Y : Finset (E d)) (g : Motion d) :
    Finset (E d) := by
  classical
  exact X.filter (fun x => g x ∈ Y)

noncomputable def matchCount {d : ℕ} (X Y : Finset (E d)) (g : Motion d) : ℕ :=
  (matchPoints X Y g).card

def richMotions {d : ℕ} (X Y : Finset (E d)) (k : ℝ) : Set (Motion d) :=
  {g | k ≤ (matchCount X Y g : ℝ)}

/-- Finiteness and the square sum, stated without choosing a finite-set witness. -/
def FiniteSquareBound {d : ℕ} (X Y : Finset (E d)) (k b : ℝ) : Prop :=
  (richMotions X Y k).Finite ∧
    ∀ G : Finset (Motion d), (∀ g ∈ G, g ∈ richMotions X Y k) →
      ∑ g ∈ G, (matchCount X Y g : ℝ) ^ 2 ≤ b

def evalR {d : ℕ} (f : Poly d) (x : E d) : ℝ := MvPolynomial.eval x f
def zeroSet {d : ℕ} (f : Poly d) : Set (E d) := {x | evalR f x = 0}
def onPolynomial {d k : ℕ} (f : Poly d) (H : Flat d k) : Prop :=
  ∀ x ∈ H.1, evalR f x = 0
def gradient (f : Poly 3) (x : E 3) : Fin 3 → ℝ :=
  fun i => evalR (MvPolynomial.pderiv i f) x

def hessian (f : Poly 3) (x : E 3) (u v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    u i * v j * evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x

def criticalPoint (f : Poly 3) (x : E 3) : Prop :=
  evalR f x = 0 ∧ ∀ i, gradient f x i = 0

def regularPoint (f : Poly 3) (x : E 3) : Prop :=
  evalR f x = 0 ∧ ∃ i, gradient f x i ≠ 0

def flatPoint (f : Poly 3) (x : E 3) : Prop :=
  regularPoint f x ∧ ∀ u v : Fin 3 → ℝ,
    (∑ i : Fin 3, gradient f x i * u i) = 0 →
    (∑ i : Fin 3, gradient f x i * v i) = 0 → hessian f x u v = 0

def criticalLine (f : Poly 3) (l : Line 3) : Prop :=
  ∀ x ∈ l.1, criticalPoint f x

def flatLine (f : Poly 3) (l : Line 3) : Prop :=
  onPolynomial f l ∧ ¬ criticalLine f l ∧
    ∀ x ∈ l.1, regularPoint f x → flatPoint f x

def inPlaneComponent (f : Poly 3) (l : Line 3) : Prop :=
  ∃ p : Poly 3, p.totalDegree = 1 ∧ p ∣ f ∧ onPolynomial p l

def mapsLine (g : Motion 3) (l l' : Line 3) : Prop :=
  g '' (l.1 : Set (E 3)) = (l'.1 : Set (E 3))

def parallel (l l' : Line 3) : Prop := l.1.direction = l'.1.direction

noncomputable def lineSeparation (l l' : Line 3) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ l.1, ∃ y ∈ l'.1, r = dist x y}

end DistinctDistances.TrackC
