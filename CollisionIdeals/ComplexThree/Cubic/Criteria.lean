module

public import CollisionIdeals.ComplexThree.Cubic.FunctionField
public import CollisionIdeals.ComplexThree.Statements.JacobianConjecture
public import CollisionIdeals.General.Automorphism.GaloisRigidity
public import CollisionIdeals.General.Automorphism.GenericDegreeOne

@[expose] public section

/-!
# Generic-degree-three criteria in complex dimension three

Generic degree three already excludes polynomial automorphisms.  On this
degree locus the counterexample condition is therefore exactly the Keller
condition.  Keller--Galois rigidity then excludes the normal cubic branch.
These criteria use the degree of the shared function-field extension and
do not require a chosen primitive generator or normal closure.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- A complex polynomial map of generic degree three is not an automorphism. -/
theorem complexThree_not_isPolynomialAutomorphism_of_finrank_eq_three
    (F : ComplexThreePolynomialMap)
    (hDegree :
      Module.finrank
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField = 3) :
    ¬ IsPolynomialAutomorphism F := by
  intro hAutomorphism
  have hOne :=
    polynomialFunctionField_finrank_eq_one_of_isPolynomialAutomorphism
      hAutomorphism
  rw [hDegree] at hOne
  norm_num at hOne

/--
For a fixed map of generic degree three, being a counterexample to `JC(3)`
is equivalent to the Keller condition.
-/
theorem complexThree_counterexample_iff_keller_of_finrank_eq_three
    (F : ComplexThreePolynomialMap)
    (hDegree :
      Module.finrank
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField = 3) :
    IsComplexThreeJacobianCounterexample F ↔ IsComplexThreeKeller F := by
  constructor
  · exact And.left
  · intro hKeller
    exact ⟨hKeller,
      complexThree_not_isPolynomialAutomorphism_of_finrank_eq_three
        F hDegree⟩

/--
Keller--Galois rigidity forces the function-field extension of a
generic-degree-three Keller map to be nonnormal.
-/
theorem complexThree_not_normal_of_finrank_eq_three
    (hRigidity : ComplexKellerGaloisRigidity 3)
    (F : ComplexThreePolynomialMap)
    (hKeller : IsComplexThreeKeller F)
    (hDegree :
      Module.finrank
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField = 3) :
    ¬ Normal
      (ComplexThreeBaseFunctionField F)
      ComplexThreeSourceFunctionField := by
  exact hRigidity.not_normal_of_counterexample
    ((complexThree_counterexample_iff_keller_of_finrank_eq_three
      F hDegree).2 hKeller)

end

end CollisionIdeals
