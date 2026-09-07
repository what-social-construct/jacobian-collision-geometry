import CollisionIdeals.General.GenericFiber.FunctionField
import CollisionIdeals.Planar.Basic

/-!
# The planar function-field degree

This file defines the marked planar generic degree.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
The finrank of the marked planar function-field extension.  On the finite
generic locus this is the usual degree `[L : K]`; the generic-degree-two API
uses the explicit positive hypothesis that it equals two.
-/
def planarGenericDegree (F : PlanarPolynomialMap) : ℕ :=
  Module.finrank
    (PolynomialBaseFunctionField F)
    (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2))

end

end CollisionIdeals
