import CollisionIdeals.Planar.Boundary.PrincipalParts
import CollisionIdeals.Planar.NormalizationDiagram
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Two planar rigidity statements

This file names the two module-theoretic criteria used in the planar paper.
They are deliberately distinct from the finiteness already built into the
normalization diagram.

* `PlanarBoundaryCoherence F` says that the first local cohomology of the
  deleted Zariski--Main boundary is finite.  This is the global-boundary
  formulation: its geometric consequence is that the whole boundary is empty.
* `PlanarRamificationRigidity` says that the already finite module of relative
  Kähler differentials on the Galois normalization has finite length.  This is
  the divisorial formulation: its immediate geometric consequence is the
  absence of height-one ramification.

The substantive geometric bridges from these statements to boundary or
ramification vanishing live in `Planar.Rigidity.Interfaces`.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- The radical ideal of the deleted intermediate-normalization boundary. -/
def planarIntermediateBoundaryIdeal (F : PlanarPolynomialMap) :
    Ideal (PolynomialIntermediateNormalizationRing F) :=
  PrimeSpectrum.vanishingIdeal
    (polynomialIntermediateNormalizationBoundary F)

/--
The global-boundary criterion: first local cohomology of the deleted boundary is
finite over the intermediate normalization ring.
-/
def PlanarBoundaryCoherence (F : PlanarPolynomialMap) : Prop :=
  BoundaryCoherence (PolynomialIntermediateNormalizationRing F)
    (planarIntermediateBoundaryIdeal F)

/--
A sufficient ramification criterion for the central `PlanarVanishing` target:
the module of relative differentials of the common Galois normalization has
finite length. This criterion is not the obstruction-vanishing statement itself.

The normalization ring is already finite over the polynomial image algebra;
finite length is the additional assertion that the differential module has
zero-dimensional support.
-/
def PlanarRamificationRigidity : Prop := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  let T := PolynomialNormalizationInExtensionRing (F := F) (N := N)
  let B := PolynomialImageAlgebra F
  letI algebraBT : Algebra B T := (integralClosure B N).algebra
  letI : SMul B T := algebraBT.toSMul
  letI : SMulCommClass B T T := Algebra.to_smulCommClass
  letI : Module T (KaehlerDifferential B T) :=
    KaehlerDifferential.module' (R := B) (S := T) (R' := T)
  exact IsFiniteLength T (KaehlerDifferential B T)

end

end CollisionIdeals.Planar
