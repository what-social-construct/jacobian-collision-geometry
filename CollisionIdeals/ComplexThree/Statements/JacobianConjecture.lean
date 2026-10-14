module

public import CollisionIdeals.ComplexThree.Basic
public import CollisionIdeals.General.Automorphism.Statements

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- Ax--Grothendieck specialized to complex affine three-space. -/
abbrev ComplexThreeAxGrothendieck : Prop :=
  ComplexAxGrothendieck 3

/-- The Jacobian conjecture in complex dimension three. -/
abbrev ComplexThreeJacobianConjecture : Prop :=
  ComplexJacobianConjecture 3

/-- A complex three-dimensional Keller map that is not an automorphism. -/
abbrev IsComplexThreeJacobianCounterexample
    (F : ComplexThreePolynomialMap) : Prop :=
  IsComplexJacobianCounterexample F

end

end CollisionIdeals
