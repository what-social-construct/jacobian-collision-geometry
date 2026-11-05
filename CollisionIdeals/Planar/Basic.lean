module

public import CollisionIdeals.General.Keller.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

/-- The coordinate ring of the complex affine plane. -/
abbrev PlanePolynomial := SourceRing ℂ (Fin 2)

/-- A polynomial self-map of the complex affine plane. -/
abbrev PlanarPolynomialMap := PolynomialSelfMap ℂ 2

/-- The Jacobian matrix of a polynomial self-map of the complex affine plane. -/
abbrev planarJacobianMatrix
    (F : PlanarPolynomialMap) :=
  jacobianMatrix F

/-- The determinant of the `2 × 2` Jacobian matrix of a planar polynomial map. -/
abbrev planarJacobianDet
    (F : PlanarPolynomialMap) : PlanePolynomial :=
  jacobianDet F

/-- A planar Keller map has a constant nonzero Jacobian determinant. -/
abbrev IsPlanarKeller
    (F : PlanarPolynomialMap) : Prop :=
  IsKeller F

end

end CollisionIdeals
