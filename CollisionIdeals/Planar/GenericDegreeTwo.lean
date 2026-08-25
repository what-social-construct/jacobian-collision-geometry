import CollisionIdeals.General.Automorphism.GaloisRigidity
import CollisionIdeals.General.Automorphism.GenericDegreeOne
import CollisionIdeals.General.ResidualCollision.Scheme
import CollisionIdeals.Planar.Basic
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.Secant.Projector

/-!
# Generic degree two for planar Keller maps

This file packages the generic-degree-two case of the planar Jacobian
conjecture.  The sole external mathematical input is the named
Keller--Galois rigidity proposition; no normalization or boundary hypothesis
is used.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
The finrank of the marked planar function-field extension.  On the finite
generic locus this is the usual degree `[L : K]`; this file uses the explicit
positive hypothesis that it equals two.
-/
def planarGenericDegree (F : PlanarPolynomialMap) : ℕ :=
  Module.finrank
    (PolynomialBaseFunctionField F)
    (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2))

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

/-- Every planar polynomial automorphism has generic degree one. -/
theorem planarGenericDegree_eq_one_of_isPolynomialAutomorphism
    {F : PlanarPolynomialMap}
    (hF : IsPolynomialAutomorphism F) :
    planarGenericDegree F = 1 :=
  polynomialFunctionField_finrank_eq_one_of_isPolynomialAutomorphism hF

/-- There is no planar Keller map of generic degree two. -/
theorem planarGenericDegree_ne_two_of_isKeller
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F) :
    planarGenericDegree F ≠ 2 := by
  intro hDegree
  have hAutomorphism : IsPolynomialAutomorphism F :=
    planarGenericDegreeTwo_isPolynomialAutomorphism
      hRigidity F hKeller hDegree
  have hDegreeOne : planarGenericDegree F = 1 :=
    planarGenericDegree_eq_one_of_isPolynomialAutomorphism hAutomorphism
  omega

/-- Equivalently, a planar map of generic degree two cannot be Keller. -/
theorem planarGenericDegreeTwo_not_keller
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hDegree : planarGenericDegree F = 2) :
    ¬ IsPlanarKeller F := by
  intro hKeller
  exact
    planarGenericDegree_ne_two_of_isKeller
      hRigidity F hKeller hDegree

/-- A planar map of generic degree two is not a Jacobian counterexample. -/
theorem planarGenericDegreeTwo_not_counterexample
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hDegree : planarGenericDegree F = 2) :
    ¬ IsComplexJacobianCounterexample F :=
  ComplexKellerGaloisRigidity.not_counterexample_of_finrank_eq_two
    hRigidity F hDegree

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

/-- Generic-degree-two rigidity identifies the collision and diagonal ideals. -/
theorem planarGenericDegreeTwo_collisionIdeal_eq_diagonalIdeal
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F)
    (hDegree : planarGenericDegree F = 2) :
    collisionIdeal F = diagonalIdeal (R := ℂ) (ι := Fin 2) :=
  (obstructionIdeal_eq_bot_iff F).1
    (planarGenericDegreeTwo_obstructionIdeal_eq_bot
      hRigidity F hKeller hDegree)

/-- The planar off-diagonal collision projector vanishes in generic degree two. -/
theorem planarGenericDegreeTwo_collisionIdempotent_eq_zero
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F)
    (hDegree : planarGenericDegree F = 2) :
    planarCollisionIdempotent F hKeller = 0 := by
  apply
    (collisionOffDiagonalProjector_eq_zero_iff_obstructionIdeal_eq_bot
      F (planarCollisionIdempotent F hKeller)
      (planarCollisionIdempotent_isProjector F hKeller)).2
  exact
    planarGenericDegreeTwo_obstructionIdeal_eq_bot
      hRigidity F hKeller hDegree

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

/-- The canonical explicit secant equations generate the unit ideal in
generic degree two. -/
theorem planarGenericDegreeTwo_explicitSecantIdeal_eq_top
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (c : ℂ) (hc : c ≠ 0)
    (hJacobian : planarJacobianDet F = MvPolynomial.C c)
    (hDegree : planarGenericDegree F = 2) :
    Planar.ExplicitSecant.explicitSecantIdeal F = ⊤ := by
  let hKeller : IsPlanarKeller F := ⟨c, hc, hJacobian⟩
  apply
    (Planar.ExplicitSecant.obstructionIdeal_eq_bot_iff_explicitSecantIdeal_eq_top
      F c hc hJacobian).1
  exact
    planarGenericDegreeTwo_obstructionIdeal_eq_bot
      hRigidity F hKeller hDegree

/-- The affine off-diagonal collision ring is zero in generic degree two. -/
theorem planarGenericDegreeTwo_offDiagonalRing_subsingleton
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F)
    (hDegree : planarGenericDegree F = 2) :
    Subsingleton (OffDiagonalRing F) :=
  (obstructionIdeal_eq_bot_iff_offDiagonalRing_subsingleton F).1
    (planarGenericDegreeTwo_obstructionIdeal_eq_bot
      hRigidity F hKeller hDegree)

/-- The affine off-diagonal collision scheme is empty in generic degree two. -/
theorem planarGenericDegreeTwo_offDiagonalVanishing
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F)
    (hDegree : planarGenericDegree F = 2) :
    CollisionOffDiagonalVanishing F :=
  (collisionOffDiagonalVanishing_iff_obstructionIdeal_eq_bot F).2
    (planarGenericDegreeTwo_obstructionIdeal_eq_bot
      hRigidity F hKeller hDegree)

end

end CollisionIdeals
