import DistinctDistances.Foundations.Projective
import DistinctDistances.OAIInterface.LocalBezout

/-! The original point-local model, below Hilbert–Samuel polynomial existence.
Declarations are relocated with their original names and literal bodies so
point-jet and carrier-length proofs can be used without an import cycle. -/

namespace DistinctDistances
noncomputable section

def pointIdeal {n : ℕ} (x : Point n) : Ideal (Poly n) :=
  MvPolynomial.vanishingIdeal ℂ {x}

instance pointIdeal_isMaximal {n : ℕ} (x : Point n) : (pointIdeal x).IsMaximal :=
  inferInstanceAs ((MvPolynomial.vanishingIdeal ℂ {x} : Ideal (Poly n)).IsMaximal)

abbrev PointLocalRing {n : ℕ} (x : Point n) := Localization.AtPrime (pointIdeal x)

def localizedIdeal {n : ℕ} (I : Ideal (Poly n)) (x : Point n) : Ideal (PointLocalRing x) :=
  I.map (algebraMap (Poly n) (PointLocalRing x))

/-- May equal `⊤`; finite length is a conclusion for isolated components only. -/
noncomputable def localLengthAt {n : ℕ} (I : Ideal (Poly n)) (x : Point n) : ℕ∞ :=
  Module.length (PointLocalRing x) (PointLocalRing x ⧸ localizedIdeal I x)

namespace AffineVariety

variable {n : ℕ}

/-- `length O_(V,x)/m_x^(t+1)`, with no conversion of infinity to zero. -/
noncomputable def localHilbert (V : AffineVariety n) (x : Point n) (t : ℕ) : ℕ∞ :=
  localLengthAt (V.ideal ⊔ pointIdeal x ^ (t+1)) x

end AffineVariety

end
end DistinctDistances

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical Topology

abbrev FieldPoint (n : ℕ) (F : Type*) := Fin n → F
abbrev FieldPoly (n : ℕ) (F : Type*) [CommSemiring F] := MvPolynomial (Fin n) F

def pointIdealOver {n : ℕ} {F : Type*} [Field F] (x : FieldPoint n F) :
    Ideal (FieldPoly n F) := MvPolynomial.vanishingIdeal F {x}

instance pointIdealOver_isMaximal {n : ℕ} {F : Type*} [Field F] (x : FieldPoint n F) :
    (pointIdealOver x).IsMaximal :=
  inferInstanceAs ((MvPolynomial.vanishingIdeal F {x} : Ideal (FieldPoly n F)).IsMaximal)

abbrev CarrierLocalRing {n : ℕ} (V : AffineVariety n) (x : Point n) :=
  PointLocalRing x ⧸ localizedIdeal V.ideal x

def localClass {n : ℕ} (V : AffineVariety n) (x : Point n) (f : Poly n) : CarrierLocalRing V x :=
  Ideal.Quotient.mk (localizedIdeal V.ideal x) (algebraMap (Poly n) (PointLocalRing x) f)

def carrierMaximalIdeal {n : ℕ} (V : AffineVariety n) (x : Point n) :
    Ideal (CarrierLocalRing V x) :=
  (pointIdeal x).map ((Ideal.Quotient.mk (localizedIdeal V.ideal x)).comp
    (algebraMap (Poly n) (PointLocalRing x)))


end
end DistinctDistances.TrackA
