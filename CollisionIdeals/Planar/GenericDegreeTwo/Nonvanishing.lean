import CollisionIdeals.General.GenericFiber.QuadraticCollision
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.GenericDegreeTwo.FunctionField

/-!
# Collision nonvanishing in planar generic degree two

Generic degree two already forces a residual generic collision sheet.  Over
the complex numbers the quadratic function-field extension is separable, so
the compatible product `L ⊗_K L ≃ L × L` descends to a nonzero affine
obstruction ideal.  For a planar Keller presentation, the canonical explicit
secant projector is therefore nonzero as well.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

/-- A planar map of generic degree two has nonzero collision obstruction. -/
theorem planarGenericDegreeTwo_obstructionIdeal_ne_bot
    (F : PlanarPolynomialMap)
    (hDegree : planarGenericDegree F = 2) :
    obstructionIdeal F ≠ ⊥ := by
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  change Module.finrank K L = 2 at hDegree
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by omega)
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : Algebra.IsSeparable K L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact polynomial_obstructionIdeal_ne_bot_of_finrank_eq_two F hDegree

/--
For a supplied Keller constant, the canonical divided-difference
off-diagonal projector is nonzero in generic degree two.
-/
theorem planarGenericDegreeTwo_explicitCollisionProjector_ne_zero
    (F : PlanarPolynomialMap)
    (c : ℂ) (hc : c ≠ 0)
    (hJacobian : planarJacobianDet F = MvPolynomial.C c)
    (hDegree : planarGenericDegree F = 2) :
    Planar.ExplicitSecant.collisionProjector F c hc ≠ 0 := by
  rw [collisionOffDiagonalProjector_ne_zero_iff_collisionIdeal_ne_diagonalIdeal
    F (Planar.ExplicitSecant.collisionProjector F c hc)
    (Planar.ExplicitSecant.collisionProjector_isProjector
      F c hc hJacobian)]
  intro hIdeals
  exact
    planarGenericDegreeTwo_obstructionIdeal_ne_bot F hDegree
      ((obstructionIdeal_eq_bot_iff F).2 hIdeals)

end

end CollisionIdeals
