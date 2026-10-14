module

public import CollisionIdeals.General.Automorphism.Criteria
public import CollisionIdeals.General.Keller.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- A polynomial self-map of complex affine `n`-space. -/
abbrev ComplexPolynomialSelfMap (n : ℕ) :=
  PolynomialSelfMap ℂ n

/--
Ax--Grothendieck in dimension `n`: an injective polynomial self-map of
complex affine `n`-space is a polynomial automorphism.
-/
def ComplexAxGrothendieck (n : ℕ) : Prop :=
  ∀ F : ComplexPolynomialSelfMap n,
    Function.Injective (pointMap F) →
      IsPolynomialAutomorphism F

/-- The Jacobian conjecture in complex dimension `n`. -/
def ComplexJacobianConjecture (n : ℕ) : Prop :=
  ∀ F : ComplexPolynomialSelfMap n,
    IsKeller F →
      IsPolynomialAutomorphism F

/-- Collision-obstruction vanishing for every complex Keller map in dimension `n`. -/
def ComplexKellerVanishing (n : ℕ) : Prop :=
  ∀ F : ComplexPolynomialSelfMap n,
    IsKeller F →
      obstructionIdeal F = ⊥

/-- A Keller map that is not a polynomial automorphism. -/
def IsComplexJacobianCounterexample
    {n : ℕ} (F : ComplexPolynomialSelfMap n) : Prop :=
  IsKeller F ∧ ¬ IsPolynomialAutomorphism F

end

end CollisionIdeals
