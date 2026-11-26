import CollisionIdeals.Planar.GenericDegreeTwo.FunctionField
import CollisionIdeals.General.GenericFiber.FunctionField

/-!
# Finite generic collision algebra

A finite planar function-field extension makes the target-generic collision
algebra finite-dimensional.  This is distinct from finiteness of the affine
collision ring over either polynomial coordinate ring.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

open scoped TensorProduct

noncomputable section

/-- The target-generic collision algebra is finite-dimensional whenever the
marked planar function-field extension has finite positive degree. -/
theorem planarGenericCollision_finiteDimensional
    (F : PlanarPolynomialMap)
    (hfinrank : 0 < Module.finrank
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2))) :
    letI : Algebra (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    FiniteDimensional (PolynomialBaseFunctionField F)
      (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
        CollisionRing F) := by
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : Algebra (polynomialMapImageAlgebra F) (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  letI : FiniteDimensional K L := FiniteDimensional.of_finrank_pos hfinrank
  let e := polynomialGenericCollisionEquiv F
    (polynomialGenericSourceTensorMap_surjective_of_finrank_pos F hfinrank)
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

end

end CollisionIdeals
