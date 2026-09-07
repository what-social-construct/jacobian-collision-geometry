import CollisionIdeals.Planar.GenericDegreeTwo.Nonvanishing
import CollisionIdeals.Planar.GenericDegreeTwo.Vanishing

/-!
# The generic-degree-two collision contradiction

Generic degree two forces a nonzero residual collision obstruction, whereas
Keller--Galois rigidity forces that same obstruction to vanish.  Their
incompatibility excludes planar Keller maps of generic degree two.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
The explicit divided-difference projector cannot simultaneously be the
nonzero quadratic residual projector and vanish by Keller--Galois rigidity.
-/
theorem planarGenericDegreeTwo_explicitProjectorContradiction
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (c : ℂ) (hc : c ≠ 0)
    (hJacobian : planarJacobianDet F = MvPolynomial.C c)
    (hDegree : planarGenericDegree F = 2) :
    False :=
  planarGenericDegreeTwo_explicitCollisionProjector_ne_zero
    F c hc hJacobian hDegree
    (planarGenericDegreeTwo_explicitCollisionProjector_eq_zero
      hRigidity F c hc hJacobian hDegree)

/-- A planar map of generic degree two cannot be Keller. -/
theorem planarGenericDegreeTwo_not_keller
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (F : PlanarPolynomialMap)
    (hDegree : planarGenericDegree F = 2) :
    ¬ IsPlanarKeller F := by
  rintro ⟨c, hc, hJacobian⟩
  exact
    planarGenericDegreeTwo_explicitProjectorContradiction
      hRigidity F c hc hJacobian hDegree

end

end CollisionIdeals
