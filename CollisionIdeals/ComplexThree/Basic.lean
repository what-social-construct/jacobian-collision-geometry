module

public import CollisionIdeals.General.Keller.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

/-- The coordinate ring of complex affine three-space. -/
abbrev ComplexThreePolynomial := SourceRing ℂ (Fin 3)

/-- A polynomial self-map of complex affine three-space. -/
abbrev ComplexThreePolynomialMap := PolynomialSelfMap ℂ 3

/-- The `3 × 3` Jacobian matrix of a polynomial self-map of
complex affine three-space. -/
abbrev complexThreeJacobianMatrix
    (F : ComplexThreePolynomialMap) :
    Matrix (Fin 3) (Fin 3) ComplexThreePolynomial :=
  jacobianMatrix F

/-- The Jacobian determinant of a polynomial self-map of
complex affine three-space. -/
abbrev complexThreeJacobianDet
    (F : ComplexThreePolynomialMap) : ComplexThreePolynomial :=
  jacobianDet F

/-- A complex three-dimensional Keller map has constant nonzero Jacobian
determinant. -/
abbrev IsComplexThreeKeller (F : ComplexThreePolynomialMap) : Prop :=
  IsKeller F

end

end CollisionIdeals
