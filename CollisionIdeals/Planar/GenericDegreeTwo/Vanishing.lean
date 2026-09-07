import CollisionIdeals.General.Automorphism.GaloisRigidity
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.GenericDegreeTwo.FunctionField

/-!
# Collision vanishing in generic degree two

Relative to the named Keller--Galois rigidity input, a planar Keller map of
generic degree two is a polynomial automorphism.  This file contains the
vanishing statements used by the collision contradiction: the obstruction
ideal and the canonical divided-difference projector both vanish.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
Keller--Galois rigidity proves the planar Jacobian conjecture on the
generic-degree-two locus.
-/
theorem planarGenericDegreeTwo_isPolynomialAutomorphism
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F)
    (hDegree : planarGenericDegree F = 2) :
    IsPolynomialAutomorphism F := by
  apply
    ComplexKellerGaloisRigidity.isPolynomialAutomorphism_of_finrank_eq_two
      hRigidity F hKeller
  exact hDegree

/-- Generic-degree-two planar Keller maps have vanishing collision obstruction. -/
theorem planarGenericDegreeTwo_obstructionIdeal_eq_bot
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F)
    (hDegree : planarGenericDegree F = 2) :
    obstructionIdeal F = ⊥ :=
  obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
    (planarGenericDegreeTwo_isPolynomialAutomorphism
      hRigidity F hKeller hDegree)

/-- The canonical divided-difference collision projector also vanishes in
generic degree two. -/
theorem planarGenericDegreeTwo_explicitCollisionProjector_eq_zero
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (c : ℂ) (hc : c ≠ 0)
    (hJacobian : planarJacobianDet F = MvPolynomial.C c)
    (hDegree : planarGenericDegree F = 2) :
    Planar.ExplicitSecant.collisionProjector F c hc = 0 := by
  let hKeller : IsPlanarKeller F := ⟨c, hc, hJacobian⟩
  apply
    (collisionOffDiagonalProjector_eq_zero_iff_obstructionIdeal_eq_bot
      F (Planar.ExplicitSecant.collisionProjector F c hc)
      (Planar.ExplicitSecant.collisionProjector_isProjector
        F c hc hJacobian)).2
  exact
    planarGenericDegreeTwo_obstructionIdeal_eq_bot
      hRigidity F hKeller hDegree

end

end CollisionIdeals
