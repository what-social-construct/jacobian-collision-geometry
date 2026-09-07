import CollisionIdeals.Planar.GenericDegreeTwo

/-!
# Solution to quadratic planar collision rigidity

This module connects the Mathlib-only Palomar statement to the project proof.
-/

set_option autoImplicit false

namespace CollisionIdeals.Palomar.PaperTwo

noncomputable section

theorem quadraticPlanarCollisionRigidity
    (hRigidity : CollisionIdeals.ComplexKellerGaloisRigidity 2)
    (F : CollisionIdeals.PlanarPolynomialMap)
    (hDegree : CollisionIdeals.planarGenericDegree F = 2) :
    CollisionIdeals.obstructionIdeal F ≠ ⊥ ∧
      ¬ CollisionIdeals.IsPlanarKeller F :=
  ⟨CollisionIdeals.planarGenericDegreeTwo_obstructionIdeal_ne_bot F hDegree,
    CollisionIdeals.planarGenericDegreeTwo_not_keller hRigidity F hDegree⟩

end

end CollisionIdeals.Palomar.PaperTwo
