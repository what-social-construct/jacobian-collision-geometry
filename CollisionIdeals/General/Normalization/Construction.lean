import CollisionIdeals.General.Normalization.ConjugateCenters
import CollisionIdeals.General.Normalization.DivisorialValuation
import CollisionIdeals.General.Normalization.PolynomialDivisorialRamification
import CollisionIdeals.General.Normalization.PolynomialDivisorialIndex

/-!
# Constructing the normalization diagram

A finite normalized cover supplies the divisorial valuations and the
double-coset centers. In characteristic zero, the divisorial ramification
theorems also supply nontrivial inertia and the local-index comparison.
The more general constructor with an explicit inertia input is retained.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- Construct the normalization diagram from a finite normalized cover
and nontrivial inertia at its ramified divisors. Valuations, centeredness,
and conjugate centers are constructed, not supplied as additional inputs. -/
def polynomialNormalizationDiagramOfInertia
    (C : PolynomialNormalizedCover (F := F) (N := N))
    (hInertia : ∀ E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N),
      inertiaGroupAt (PolynomialMapBaseFunctionField F)
        (polynomialDivisorialValuation C.normalClosure E.1 E.2.1).valuationRing ≠ ⊥) :
    PolynomialNormalizationDiagram (F := F) (N := N) where
  cover := C
  valuationAt E := polynomialDivisorialValuation C.normalClosure E.1 E.2.1
  valuation_centered E := polynomialDivisorialValuation_centered C.normalClosure E.1 E.2.1
  inertia_nontrivial := hInertia
  centerAtClass E := polynomialConjugateCenterAtClass C.normalClosure E.1
    (polynomialDivisorialValuation C.normalClosure E.1 E.2.1)
    (polynomialDivisorialValuation_centered C.normalClosure E.1 E.2.1)
  centerAtClass_mapsToBase E := polynomialConjugateCenterAtClass_mapsToBase
    C.normalClosure E.1
    (polynomialDivisorialValuation C.normalClosure E.1 E.2.1)
    (polynomialDivisorialValuation_centered C.normalClosure E.1 E.2.1)
  baseClass_center E := polynomialConjugateCenterAtClass_one C.normalClosure E.1
    (polynomialDivisorialValuation C.normalClosure E.1 E.2.1)
    (polynomialDivisorialValuation_centered C.normalClosure E.1 E.2.1)
  centerAtRepresentative E g := polynomialConjugateCenterAtClass_mk C.normalClosure E.1
    (polynomialDivisorialValuation C.normalClosure E.1 E.2.1)
    (polynomialDivisorialValuation_centered C.normalClosure E.1 E.2.1) g

/-- In characteristic zero, the finite normalized cover supplies the whole
normalization diagram, including nontrivial inertia at ramified divisors. -/
def polynomialNormalizationDiagramOfCover [CharZero k]
    (C : PolynomialNormalizedCover (F := F) (N := N)) :
    PolynomialNormalizationDiagram (F := F) (N := N) :=
  polynomialNormalizationDiagramOfInertia C
    (polynomialRamifiedPoint_inertia_nontrivial C.normalClosure)

/-- The constructed diagram realizes every conjugate inertia index as the
actual local ramification index. No index comparison is supplied as input. -/
theorem polynomialNormalizationDiagramOfCover_ramificationRealization [CharZero k]
    (C : PolynomialNormalizedCover (F := F) (N := N)) :
    (polynomialNormalizationDiagramOfCover C).ConjugateRamificationRealization := by
  apply PolynomialNormalizationDiagram.ConjugateRamificationRealization.ofIndexEquality
  intro E q
  refine Quotient.inductionOn q ?_
  intro g
  exact (polynomialConjugateCenter_localRamificationIndex_eq
    C.normalClosure E.1 E.2.1 g).symm

end

end CollisionIdeals
