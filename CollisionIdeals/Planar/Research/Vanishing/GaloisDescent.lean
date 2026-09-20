import CollisionIdeals.General.Automorphism.GaloisRigidity
import CollisionIdeals.General.Galois.PolynomialDescent
import CollisionIdeals.General.Keller.GenericFiniteness
import CollisionIdeals.Planar.Statements.JacobianConjecture
import CollisionIdeals.Planar.Statements.Vanishing

/-!
# The Galois-descent target for planar vanishing

For each complex planar Keller map, use its canonical marked normal closure
`D : NormalClosureData K L N`. The proposed target asks that every conjugate
of either source coordinate belongs to the marked original field `D.intermediateField`.
This is rational descent to `L`, not regularity in a normalization ring or
pointwise fixing of the coordinates.

The target is equivalent to normality of the original extension `L/K`.
Normality of `N/K`, already supplied by the construction, does not prove it.
With the explicit Keller--Galois rigidity input, the target implies polynomial
invertibility and obstruction vanishing. The target itself remains unproved;
it is a proposition, not an axiom or a supplied instance.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/-- Every normal-closure conjugate of each planar source coordinate descends
to the marked original source function field. This unrestricted complex-planar
statement is an open theorem target, not an assumption added to the environment. -/
def PlanarGaloisDescent : Prop :=
  ∀ (F : PlanarPolynomialMap) (hKeller : IsKeller F),
    let D := polynomialCanonicalNormalClosureData F hKeller
    ∀ (g : D.galoisGroup) (i : Fin 2),
      g (D.embedding
        (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F)
          (MvPolynomial.X i))) ∈ D.intermediateField

/-- Coordinate descent is exactly the missing original-extension normality
statement, not an additional consequence of normal-closure existence. -/
theorem planarGaloisDescent_iff_forall_normal :
    PlanarGaloisDescent ↔
      ∀ F : PlanarPolynomialMap, IsKeller F →
        Normal (PolynomialMapBaseFunctionField F)
          (PolynomialMapSourceFunctionField F) := by
  constructor
  · intro hDescent F hKeller
    exact (polynomialSource_normal_iff_conjugate_coordinates_mem
      (polynomialCanonicalNormalClosureData F hKeller)).mpr (hDescent F hKeller)
  · intro hNormal F hKeller
    exact (polynomialSource_normal_iff_conjugate_coordinates_mem
      (polynomialCanonicalNormalClosureData F hKeller)).mp (hNormal F hKeller)

/-- The descent target supplies precisely the normality premise needed by
the explicit classical Keller--Galois rigidity input. -/
theorem planarJacobianConjecture_of_galoisDescent
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (hDescent : PlanarGaloisDescent) :
    PlanarJacobianConjecture := by
  intro F hKeller
  exact hRigidity F hKeller
    (planarGaloisDescent_iff_forall_normal.mp hDescent F hKeller)

/-- Galois descent and the stated rigidity input imply the existing planar
obstruction-vanishing target. No Ax--Grothendieck or purity input is needed. -/
theorem planarVanishing_of_galoisDescent
    (hRigidity : ComplexKellerGaloisRigidity 2)
    (hDescent : PlanarGaloisDescent) :
    PlanarVanishing := by
  intro F hKeller
  exact obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
    (planarJacobianConjecture_of_galoisDescent hRigidity hDescent F hKeller)

end

end CollisionIdeals.Planar
