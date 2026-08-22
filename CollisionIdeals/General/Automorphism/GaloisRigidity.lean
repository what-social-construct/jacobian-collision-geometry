import CollisionIdeals.General.Automorphism.Statements
import CollisionIdeals.General.GenericFiber.FunctionField
import Mathlib.FieldTheory.Normal.Basic

/-!
# Keller--Galois rigidity

This file records the classical complex theorem that a Keller map whose
induced function-field extension is normal is a polynomial automorphism.
The result is exposed as a theorem target rather than assumed as an axiom.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
Keller--Galois rigidity in complex dimension `n`: if the function-field
extension induced by a Keller map is normal, then the map is a polynomial
automorphism.

This proposition is a theorem target.  It packages the classical external
input separately from the elementary collision and cubic Galois arguments.
-/
def ComplexKellerGaloisRigidity (n : ℕ) : Prop :=
  ∀ F : ComplexPolynomialSelfMap n,
    IsKeller F →
      Normal
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := ℂ) (ι := Fin n)) →
      IsPolynomialAutomorphism F

/--
Under Keller--Galois rigidity, the function-field extension of a complex
Jacobian counterexample cannot be normal.
-/
theorem ComplexKellerGaloisRigidity.not_normal_of_counterexample
    {n : ℕ}
    (hRigidity : ComplexKellerGaloisRigidity n)
    {F : ComplexPolynomialSelfMap n}
    (hF : IsComplexJacobianCounterexample F) :
    ¬ Normal
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin n)) := by
  intro hNormal
  exact hF.2 (hRigidity F hF.1 hNormal)

end

end CollisionIdeals
